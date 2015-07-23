{-# LANGUAGE KindSignatures, RankNTypes, GADTs, OverloadedStrings #-}

module SneathLane
       (
         -- * Widgets
         Widget(..),
         WidgetFocus(..),
         zipW,

         -- * Build Widgets
         graphicWidget,
         above,
         beside,

         -- * Run Widgets
         runOnCanvas,

         -- * Graphics
         GraphicTree(..),
         graphicList,
         graphicTreeBounds,

         -- * Events
         MouseButton(..),
         Key,

         -- * Utility
         balancedFold,

         -- * Type synonyms
         Output,
         CombineGraphics,
         Animate,
         MouseOut,
         HandleKey,
         TimeDifference
       )
       where

import Control.Applicative (Applicative(..), liftA2)
import Control.Monad (mplus)
import Data.Functor ((<$))
import Data.Maybe (fromMaybe)
import Data.IORef (newIORef, readIORef, writeIORef, modifyIORef)

import Haste (elemById, writeLog, onEvent, setTimeout, focus, blur, mkCallback, attr, style, set, (=:), Event (..), Elem, JSFun, JSString)
import Haste.Foreign (ffi)
import SneathLane.Graphics

-- | Which mouse button (if any) was being pressed
data MouseButton = NoButton | LeftButton

type Key = Int

-- | A tree of graphics, used as widget output type. FMap functions are stored in the tree
-- instead of being mapped over the leaves, so that tree reconstruction is fast when a widget changes.
-- This is why GraphicTree is a GADT.
--
-- Offset: a sub-tree translated by a point
--
-- Branch: Two sub-trees; graphicTreeBounds are cached for each
--
-- Leaf: A leaf, consisting of a single graphic element
--
-- FMap: A graphic tree composed with a function.

data GraphicTree :: * -> * where
  Offset :: Point -> GraphicTree a -> GraphicTree a
  Branch :: Rect -> GraphicTree a -> Rect -> GraphicTree a -> GraphicTree a
  Leaf :: Graphic -> GraphicTree ()
  FMap :: (a -> b) -> GraphicTree a -> GraphicTree b

instance Functor GraphicTree where
  fmap = FMap

-- | Construct a graphic tree from a nonempty list of graphics.
graphicList :: [Graphic] -> GraphicTree ()
graphicList gs = balancedFold (\g g' -> Branch (graphicTreeBounds g) g (graphicTreeBounds g') g') (map (\g -> Leaf g) gs)

-- | Apply a fold in a balanced fashion over a list. Recommended for
-- combining lists of widgets, so that the widget tree has
-- logarithmic depth.

balancedFold :: (a -> a -> a) -> [a] -> a
balancedFold _ [] = error "balancedFold: empty list"
balancedFold _ [x] = x
balancedFold fn xs = balancedFold fn (combinePairs xs)
  where
    combinePairs [] = []
    combinePairs [x] = [x]
    combinePairs (x:y:xs') = fn x y : combinePairs xs'


graphicAtPoint :: Point -> GraphicTree a -> Maybe (Point, a)
graphicAtPoint (x,y) gt = case gt of
  Offset (x',y') gt' -> graphicAtPoint (x - x', y - y') gt'
  Branch bounds gt' bounds' gt'' ->
    case ((x,y) `inRect` bounds, (x,y) `inRect` bounds') of
      (False, False) -> Nothing
      (False, True) -> graphicAtPoint (x,y) gt''
      (True, False) -> graphicAtPoint (x,y) gt'
      (True, True) -> graphicAtPoint (x,y) gt'' `mplus` graphicAtPoint (x,y) gt'
  Leaf g -> if (x,y) `inGraphic` g then Just ((x,y), ()) else Nothing
  FMap fn gt' -> fmap (\(pt,a) -> (pt, fn a)) (graphicAtPoint (x,y) gt')


drawGraphicTree :: Canvas -> GraphicTree a -> IO ()
drawGraphicTree canv gt = render canv $ go (0,0) gt
  where
    go :: Point -> GraphicTree a -> Picture ()
    go (x,y) (Offset (x',y') gt') = go (x + x', y + y') gt'
    go pt (Branch _ gt' _ gt'') = go pt gt' >> go pt gt''
    go pt (FMap _ gt') = go pt gt'
    go pt (Leaf g) = drawGraphic g pt


-- | Find a rectangle containing the entire contents of the graphic tree
graphicTreeBounds :: GraphicTree a -> Rect
graphicTreeBounds gt = case gt of
  Offset (x,y) gt' -> let (Rect x' y' w h) = graphicTreeBounds gt' in Rect (x+x') (y+y') w h
  Branch (Rect x y w h) _ (Rect x' y' w' h') _ -> Rect (min x x') (min y y') (max (x + w) (x' + w') - min x x') (max (y + h) (y' + h') - min y y')
  FMap _ gt' -> graphicTreeBounds gt'
  Leaf g -> graphicBounds g

type Output a = GraphicTree ((Point,MouseButton) -> a)

type MouseOut a = a

type HandleKey a = Key -> a

type TimeDifference = Double

type Animate a = TimeDifference -> a

-- | Atom of a sneath lane application
data Widget z = Finish z
              | Continue (Output (Widget z)) (Maybe (MouseOut (Widget z))) (Maybe (Animate (Widget z))) (WidgetFocus z)

-- | Determines the focus behavior of the widget
data WidgetFocus z = NotFocusable -- ^ Widget can not take keyboard focus
                   | Focusable (Widget z) (Widget z) -- ^ Widget can take keyboard focus, but does not have it now
                   | Focused (Widget z) (Widget z, Bool) (Widget z, Bool) (HandleKey (Widget z)) -- ^ Widget has keyboard focus

type CombineGraphics a = GraphicTree a -> GraphicTree a -> GraphicTree a

-- | Combine two widgets to run in parallel as a single widget
zipW :: CombineGraphics ((Point, MouseButton) -> Widget z) -> Widget z -> Widget z -> Widget z

bindW :: (a -> Widget b) -> Widget a -> Widget b
bindW fn (Finish w) = fn w
bindW fn (Continue out mouseOut anim foc) =
  let
    out' = (fmap.fmap) (bindW fn) out
    mouseOut' = fmap (bindW fn) mouseOut
    anim' = (fmap.fmap) (bindW fn) anim
    foc' = case foc of
      NotFocusable -> NotFocusable
      Focusable fromLeft fromRight -> Focusable (bindW fn fromLeft) (bindW fn fromRight)
      Focused blur (tabLeft,ld) (tabRight,rd) key -> Focused (bindW fn blur) (bindW fn tabLeft,ld) (bindW fn tabRight,rd) (fmap (bindW fn) key)
  in Continue out' mouseOut' anim' foc'

instance Functor Widget where
  fmap fn = bindW (Finish . fn)

instance Applicative Widget where
  pure = Finish

  (<*>) wf w = bindW (\fn -> bindW (Finish . fn) w) wf

instance Monad Widget where
  return = Finish

  (>>=) = flip bindW


zipW comb lw rw = case (lw, rw) of
  (Finish z, _) -> Finish z
  (_, Finish z) -> Finish z

  (Continue _ _ _ (Focused blur _ _ _), Continue _ _ _ (Focused _ _ _ _)) -> zipW comb blur rw

  (Continue out mouseOut anim foc, Continue out' mouseOut' anim' foc') ->
    let
      updateLeft lw' rw' = case (lw', rw') of
        (Continue _ _ _ (Focused _ _ _ _), Continue _ _ _ (Focused blur _ _ _)) -> zipW comb lw' blur
        _ -> zipW comb lw' rw'

      out'' = comb
              ((fmap.fmap) (\lw' -> updateLeft lw' (fromMaybe rw mouseOut')) out)
              ((fmap.fmap) (\rw' -> zipW comb (fromMaybe lw mouseOut) rw') out')

      mouseOut'' = case (mouseOut, mouseOut') of
        (Nothing, Nothing) -> Nothing
        (Just lw', Nothing) -> Just $ updateLeft lw' rw
        (_, Just rw') -> Just $ zipW comb (fromMaybe lw mouseOut) rw'

      anim'' = case (anim, anim') of
        (Nothing, Nothing) -> Nothing
        (Just animFn, Nothing) -> Just $ \t -> updateLeft (animFn t) rw
        (_, Just animFn') -> Just $ liftA2 (zipW comb) (fromMaybe (const lw) anim) animFn'

      foc'' = case (foc, foc') of
        (NotFocusable, NotFocusable) -> NotFocusable
        (Focused _ _ _ _, Focused _ _ _ _) -> error "paired focus elements should cause blur above"

        (NotFocusable, Focusable fromLeft fromRight) -> Focusable (zipW comb lw fromLeft) (zipW comb lw fromRight)
        (Focusable fromLeft fromRight, NotFocusable) -> Focusable (updateLeft fromLeft rw) (updateLeft fromRight rw)
        (Focusable fromLeft _, Focusable _ fromRight) -> Focusable (updateLeft fromLeft rw) (zipW comb lw fromRight)

        (Focused blur (tabLeft,ld) (tabRight,False) key, Focusable fromLeft _) ->
          Focused (updateLeft blur rw) (updateLeft tabLeft rw, ld) (updateLeft tabRight fromLeft, True) (fmap (\lw' -> updateLeft lw' rw) key)
        (Focusable _ fromRight, Focused blur (tabLeft,False) (tabRight,rd) key) ->
          Focused (zipW comb lw blur) (zipW comb fromRight tabLeft, True) (zipW comb lw tabRight, rd) (fmap (\rw' -> zipW comb lw rw') key)

        (Focused blur (tabLeft,ld) (tabRight,rd) key, _) ->
          Focused (updateLeft blur rw) (updateLeft tabLeft rw, ld) (updateLeft tabRight rw, rd) (fmap (\lw' -> updateLeft lw' rw) key)
        (_, Focused blur (tabLeft,ld) (tabRight,rd) key) ->
          Focused (zipW comb lw blur) (zipW comb lw tabLeft, ld) (zipW comb lw tabRight, rd) (fmap (\rw' -> zipW comb lw rw') key)
    in Continue out'' mouseOut'' anim'' foc''


jsNow :: IO Double
jsNow = ffi "(function() { return new Date().getTime(); })"

jsKeyDown :: Elem -> (Int -> Bool -> IO Bool) -> IO ()
jsKeyDown = ffi "(function(elem, onKey) { elem.addEventListener('keydown', function(ev) { if(!onKey(ev.keyCode,ev.shiftKey)){ev.preventDefault();} })})"

jsRequestAnimationFrame :: (() -> IO ()) -> IO ()
jsRequestAnimationFrame = ffi "(function(fn) { window.requestAnimationFrame(fn); })"

-- | Run the widget on the canvas element with ID "canvas"
runOnCanvas :: String -> Double -> Double -> (forall z. Widget z) -> IO ()
runOnCanvas elemId width height w = do
  wref <- newIORef w
  Just ce <- elemById elemId
  set ce [attr "width" =: show (pixelRatio * width),
          attr "height" =: show (pixelRatio * height),
          style "width" =: (show width ++ "px"),
          style "height" =: (show height ++ "px")]
  (Just canvas) <- getCanvas ce
  ce `onEvent` OnMouseDown $ (\_ pt -> modifyIORef wref (mouseEvent (fromIntegral $ fst pt, fromIntegral $ snd pt) LeftButton) >> adjustFocus ce wref)
  ce `onEvent` OnMouseMove $ (\pt -> modifyIORef wref (mouseEvent (fromIntegral $ fst pt, fromIntegral $ snd pt) NoButton) >> adjustFocus ce wref)
  jsKeyDown ce (\key shift -> keyEvent wref key shift)
  --ce `onEvent` OnKeyDown $ (\key -> modifyIORef wref (keyEvent key) >> adjustFocus ce wref)

  tm <- jsNow
  renderFrame 16.0 tm canvas wref
  return ()
    where
      adjustFocus ce wref = do
        Continue _ _ _ foc <- readIORef wref
        case foc of
          Focused _ _ _ _ -> focus ce
          _ -> blur ce

      renderFrame mspf prevTime canvas wref = do
        Continue out _ anim _ <- readIORef wref
        drawGraphicTree canvas out
        tm <- jsNow
        case anim of
          Just fn -> writeIORef wref (fn $ tm - prevTime)
          _ -> return ()
        let mspf' = mspf*0.95 + (tm - prevTime)*0.05
        --writeLog (show $ floor $ 1000/mspf')
        jsRequestAnimationFrame (\_ -> renderFrame mspf' tm canvas wref)

      mouseEvent _ _ (Finish _) = error "top-level finish"
      mouseEvent pt button w'@(Continue out mouseOut _ _) =
        case graphicAtPoint pt out of
          Nothing -> fromMaybe w' mouseOut
          Just (oset, fw) -> fw (oset, button)

      keyEvent wref key shift = do
        Continue _ _ _ foc <- readIORef wref
        case (key,shift) of
          (9,False) -> case foc of
            Focused _ _ (tabRight, rd) _ -> writeIORef wref tabRight >> return (not rd)
            Focusable fromLeft _ -> writeIORef wref fromLeft >> return False
          (9,True) -> case foc of
            Focused _ (tabLeft, ld) _ _ -> writeIORef wref tabLeft >> return (not ld)
            Focusable _ fromRight -> writeIORef wref fromRight >> return False
          _ -> case foc of
            Focused _ _ _ onKey -> case onKey key of
              w'@(Continue _ _ _ (Focused _ _ _ _)) -> writeIORef wref w' >> return False
              w' -> writeIORef wref w' >> return True


-- | A widget which just shows a constant graphic output.
graphicWidget :: GraphicTree () -> Widget a
graphicWidget g = Continue (const (graphicWidget g) <$ g) Nothing Nothing NotFocusable

combineBeside :: CombineGraphics a
combineBeside gt gt' =
  let bounds@(Rect l t w h) = graphicTreeBounds gt
      (Rect l' t' w' h') = graphicTreeBounds gt'
  in Branch bounds gt (Rect (l + w) t' w' h') (Offset (l + w - l', 0) gt')

-- | Combine two widgets side by side
beside :: Widget z -> Widget z -> Widget z
beside = zipW combineBeside

combineAbove :: CombineGraphics a
combineAbove gt gt' =
  let bounds@(Rect l t w h) = graphicTreeBounds gt
      (Rect l' t' w' h') = graphicTreeBounds gt'
  in Branch bounds gt (Rect l' (t+h) w' h') (Offset (0, t + h - t') gt')

-- | Combine two widgets one above the other
above :: Widget z -> Widget z -> Widget z
above = zipW combineAbove

{-
hoverWidget :: GraphicTree () -> GraphicTree () -> Widget a
hoverWidget g1 g2 = outside
  where
    outside = Continue (Leaf g1 (const inside)) Nothing Nothing NotFocusable
    inside = Continue (Leaf g2 (const inside)) (Just outside) Nothing NotFocusable
-}

{-
hw = hoverWidget (Graphic (Rect 0 0 40 40) (RGBA 100 200 100)) (Graphic (Rect 0 0 40 40) (RGBA 200 100 100))

hw' = hoverWidget' (\frac -> Graphic (Rect 0 0 40 40) (RGBA (floor $ frac * 100) 100 100))


main :: IO ()
main = runOnCanvas (seven `above` seven)
  where
    one = hw' `beside` hw'
    two = one `beside` one
    three = two `beside` two
    four = three `beside` three
    five = four `above` four
    six = five `above` five
    seven = six `above` six

-}
