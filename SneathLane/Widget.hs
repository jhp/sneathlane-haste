{-# LANGUAGE KindSignatures, RankNTypes, GADTs, OverloadedStrings #-}

module SneathLane.Widget
       (
         -- * Widgets
         Widget(..),
         WidgetFocus(..),
         zipW,

         -- * Build Widgets
         graphicWidget,
         above,
         combineAbove,
         beside,
         combineBeside,
         mapGraphic,
         mapWidgetFocus,

         -- * Run Widgets
         runOnCanvas,

         -- * Graphics
         GraphicTree(..),
         graphicList,
         graphicTreeBounds,

         -- * Events
         MouseEv(..),
         MouseButton(..),
         Key(..),

         -- * Utility
         balancedFold,

         -- * Type synonyms
         OutputFn,
         Animate,
         MouseOut,
         HandleKey,
         TimeDifference
       )
       where

import Control.Applicative (Applicative(..), liftA2)
import Control.Monad (mplus, when)
import Data.Functor ((<$))
import Data.Maybe (fromMaybe)
import Data.IORef (newIORef, readIORef, writeIORef, modifyIORef)

import Control.Arrow ((***))

import Haste
import Haste.DOM
import Haste.Graphics.AnimationFrame
import qualified Haste.Graphics.Canvas as HC
import Haste.Foreign
import Haste.Events hiding (MouseButton)
import SneathLane.Graphics

import System.IO.Unsafe (unsafePerformIO)
logging x y = unsafePerformIO (writeLog (show x) >> return y)

data MouseEv = EvMouseUp Point MouseButton | EvMouseDown Point MouseButton | EvMouseMove Point

getMousePoint mev = case mev of
  EvMouseUp pt _ -> pt
  EvMouseDown pt _ -> pt
  EvMouseMove pt -> pt

setMousePoint mev pt = case mev of
  EvMouseUp _ b -> EvMouseUp pt b
  EvMouseDown _ b -> EvMouseDown pt b
  EvMouseMove _ -> EvMouseMove pt

-- | Which mouse button (if any) was being pressed
data MouseButton = RightButton | LeftButton

data Key = EvKeyDown Int Bool | EvKeyUp Int Bool | EvKeyInput JSString

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
  Clip :: Rect -> GraphicTree a -> GraphicTree a
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
  Clip rect gt' -> if (x,y) `inRect` rect then graphicAtPoint (x,y) gt' else Nothing
  Offset (x',y') gt' -> graphicAtPoint (x - x', y - y') gt'
  Branch bounds gt' bounds' gt'' ->
    case ((x,y) `inRect` bounds, (x,y) `inRect` bounds') of
      (False, False) -> Nothing
      (False, True) -> graphicAtPoint (x,y) gt''
      (True, False) -> graphicAtPoint (x,y) gt'
      (True, True) -> graphicAtPoint (x,y) gt'' `mplus` graphicAtPoint (x,y) gt'
  Leaf g -> if (x,y) `inGraphic` g then Just ((x,y), ()) else Nothing
  FMap fn gt' -> fmap (\(pt,a) -> (pt, fn a)) (graphicAtPoint (x,y) gt')

refineBounds :: Rect -> Rect -> Maybe Rect
refineBounds (Rect x y w h) (Rect x' y' w' h') =
  let x'' = max x x'
      y'' = max y y'
      w'' = min (x + w) (x' + w') - x''
      h'' = min (y + h) (y' + h') - y''
  in if w'' > 0 && h'' > 0
     then Just (Rect x'' y'' w'' h'')
     else Nothing

drawGraphicTree :: Canvas -> GraphicTree a -> IO ()
drawGraphicTree canv gt = render canv $ go (0,0) Nothing gt
  where
    go :: Point -> Maybe Rect -> GraphicTree a -> Picture ()
    go (x,y) bounds (Offset (x',y') gt') = let bounds' = case bounds of
                                                 Nothing -> Nothing
                                                 Just (Rect x y w h) -> Just (Rect (x - x') (y - y') w h)
                                           in go (x + x', y + y') bounds' gt'
    go pt bounds (Clip rect gt') = go pt (maybe (Just rect) (refineBounds rect) bounds) gt'
    go pt bounds (Branch bounds' gt' bounds'' gt'') = case bounds of
                                                           Nothing -> go pt Nothing gt' >> go pt Nothing gt''
                                                           Just rect -> do
                                                             maybe (return ()) (\b -> go pt (Just b) gt') (refineBounds rect bounds')
                                                             maybe (return ()) (\b -> go pt (Just b) gt'') (refineBounds rect bounds'')
    go pt bounds (FMap _ gt') = go pt bounds gt'
    go pt@(x',y') bounds (Leaf g) =
      let pic = drawGraphic g pt
      in case bounds of
      Just (Rect x y w h) -> HC.clip (HC.rect (x+x',y+y') (x+w+x',y+h+y')) pic
      Nothing -> pic


-- | Find a rectangle containing the entire contents of the graphic tree
graphicTreeBounds :: GraphicTree a -> Rect
graphicTreeBounds gt = case gt of
  Clip rect _ -> rect
  Offset (x,y) gt' -> let (Rect x' y' w h) = graphicTreeBounds gt' in Rect (x+x') (y+y') w h
  Branch (Rect x y w h) _ (Rect x' y' w' h') _ -> Rect (min x x') (min y y') (max (x + w) (x' + w') - min x x') (max (y + h) (y' + h') - min y y')
  FMap _ gt' -> graphicTreeBounds gt'
  Leaf g -> graphicBounds g

type OutputFn f z = MouseEv -> (Maybe String, Widget f z)

type MouseOut a = a

type HandleKey a = Key -> a

type TimeDifference = Double

type Animate a = TimeDifference -> a

-- | Atom of a sneath lane application
data Widget f z = Finish z
              | Continue (f (OutputFn f z)) (Maybe (MouseOut (Widget f z))) (Maybe (Animate (Widget f z))) (WidgetFocus f z)

-- | Determines the focus behavior of the widget
data WidgetFocus f z = NotFocusable -- ^ Widget can not take keyboard focus
                     | Focusable (Widget f z) (Widget f z) -- ^ Widget can take keyboard focus, but does not have it now
                     | Focused (Widget f z) (Widget f z, Bool) (Widget f z, Bool) (HandleKey (Widget f z)) -- ^ Widget has keyboard focus

bindW :: (Functor f) => (a -> Widget f b) -> Widget f a -> Widget f b
bindW fn (Finish w) = fn w
bindW fn (Continue out mouseOut anim foc) =
  let
    out' = (fmap.fmap) (id *** bindW fn) out
    mouseOut' = fmap (bindW fn) mouseOut
    anim' = (fmap.fmap) (bindW fn) anim
    foc' = case foc of
      NotFocusable -> NotFocusable
      Focusable fromLeft fromRight -> Focusable (bindW fn fromLeft) (bindW fn fromRight)
      Focused blur (tabLeft,ld) (tabRight,rd) key -> Focused (bindW fn blur) (bindW fn tabLeft,ld) (bindW fn tabRight,rd) (fmap (bindW fn) key)
  in Continue out' mouseOut' anim' foc'

instance (Functor f) => Functor (Widget f) where
  fmap fn = bindW (Finish . fn)

instance (Functor f) => Applicative (Widget f) where
  pure = Finish

  (<*>) wf w = bindW (\fn -> bindW (Finish . fn) w) wf

instance (Functor f) => Monad (Widget f) where
  return = Finish

  (>>=) = flip bindW


-- | Combine two widgets to run in parallel as a single widget
zipW :: (Functor f, Functor g, Functor h) => (f (OutputFn h z) -> g (OutputFn h z) -> h (OutputFn h z)) -> Widget f z -> Widget g z -> Widget h z
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
              ((fmap.fmap) (\(murl,lw') -> (murl, updateLeft lw' (fromMaybe rw mouseOut'))) out)
              ((fmap.fmap) (\(murl,rw') -> (murl, zipW comb (fromMaybe lw mouseOut) rw')) out')

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
jsKeyDown = ffi "(function(elem, onKey) { elem.addEventListener('keydown', function(ev) { if(!onKey(ev.keyCode,ev.shiftKey)){ev.preventDefault();} }) })"

jsKeyUp :: Elem -> (Int -> Bool -> IO Bool) -> IO ()
jsKeyUp = ffi "(function(elem, onKey) { elem.addEventListener('keyup', function(ev) { if(!onKey(ev.keyCode,ev.shiftKey)){ev.preventDefault();} })})"

jsKeyInput :: Elem -> (JSString -> IO JSString) -> IO ()
jsKeyInput = ffi "(function(elem, onKey) { elem.addEventListener('input', function(ev) { elem.value = onKey(elem.value); }) })"

jsRequestAnimationFrame :: (() -> IO ()) -> IO ()
jsRequestAnimationFrame = ffi "(function(fn) { window.requestAnimationFrame(fn); })"

jsOnResize :: (() -> IO ()) -> IO ()
jsOnResize = ffi "(function(fn) { window.onresize = fn; })"

jsGetWidth :: IO Double
jsGetWidth = ffi "(function() { return window.innerWidth; })"

jsGetHeight :: IO Double
jsGetHeight = ffi "(function() { return window.innerHeight; })"

jsRemoveHref :: Elem -> IO ()
jsRemoveHref = ffi "(function(elem) { elem.removeAttribute('href'); })"

-- | Create a Canvas element filling the browser viewport, and run the given Widget there
runOnCanvas :: (forall z. Double -> Widget GraphicTree z) -> IO ()
runOnCanvas fw = do
  atag <- newElem "a"
  ce <- newElem "canvas"
  (Just canvas) <- getCanvas ce

  keyInput <- newElem "input"
  set keyInput [attr "type" =: "text",
             style "position" =: "absolute",
             style "left" =: "-1000px"]
  appendChild documentBody keyInput

  appendChild documentBody atag
  appendChild atag ce

  ww <- jsGetWidth
  wref <- newIORef (fw ww)

  ce `onEvent` MouseDown $ (\ev -> mouseEvent atag (EvMouseDown (fromIntegral $ fst $ mouseCoords ev, fromIntegral $ snd $ mouseCoords ev) LeftButton) wref >> adjustFocus keyInput wref)
  ce `onEvent` MouseUp $ (\ev -> mouseEvent atag (EvMouseUp (fromIntegral $ fst $ mouseCoords ev, fromIntegral $ snd $ mouseCoords ev) LeftButton) wref >> adjustFocus keyInput wref)
  ce `onEvent` MouseMove $ (\ev -> mouseEvent atag (EvMouseMove (fromIntegral $ fst $ mouseCoords ev, fromIntegral $ snd $ mouseCoords ev)) wref >> adjustFocus keyInput wref)

  jsKeyDown keyInput (\key shift -> keyEvent wref (EvKeyDown key shift))
  jsKeyInput keyInput (\str -> keyEvent wref (EvKeyInput str) >> return "")
  jsKeyUp keyInput (\key shift -> keyEvent wref (EvKeyUp key shift))

  jsOnResize (\_ -> do
                 ww <- jsGetWidth
                 writeIORef wref (fw ww))

  tm <- jsNow
  renderFrame 16.0 tm ce canvas wref
  return ()
    where
      adjustFocus elem wref = do
        Continue _ _ _ foc <- readIORef wref
        case foc of
          Focused _ _ _ _ -> focus elem
          _ -> blur elem

      renderFrame mspf prevTime ce canvas wref = do
        Continue out _ anim _ <- readIORef wref

        let Rect ox oy ow oh = graphicTreeBounds out

        set ce [attr "width" =: show (pixelRatio * (ox + ow)),
                attr "height" =: show (ceiling $ pixelRatio * (oy + oh)),
                style "width" =: (show (ox + ow) ++ "px"),
                style "height" =: (show (ceiling $ oy + oh) ++ "px")]

        drawGraphicTree canvas out
        tm <- jsNow
        case anim of
          Just fn -> writeIORef wref (fn $ (tm - prevTime) / 1000)
          _ -> return ()
        let mspf' = mspf*0.95 + (tm - prevTime)*0.05
        --writeLog (show $ floor $ 1000/mspf')
        requestAnimationFrame (\_ -> renderFrame mspf' tm ce canvas wref)
        return ()

      mouseEvent atag mev wref = do
        Continue out mouseOut _ _ <- readIORef wref
        let pt = getMousePoint mev

        case graphicAtPoint pt out of
          Nothing -> do
            jsRemoveHref atag
            case mouseOut of
              Just w' -> writeIORef wref w'
              _ -> return ()
          Just (oset, fw) -> do
            let (murl, w') = fw (setMousePoint mev oset)
            case murl of
              Just url -> do
                currUrl <- getAttr atag "href"
                when (currUrl /= url) (set atag [attr "href" =: url])
              Nothing -> jsRemoveHref atag
            writeIORef wref w'

      keyEvent wref kEv = do
        Continue _ _ _ foc <- readIORef wref
        case kEv of
          EvKeyDown 9 False -> case foc of
            Focused _ _ (tabRight, rd) _ -> writeIORef wref tabRight >> return (not rd)
            Focusable fromLeft _ -> writeIORef wref fromLeft >> return False
            _ -> return True

          EvKeyDown 9 True -> case foc of
            Focused _ (tabLeft, ld) _ _ -> writeIORef wref tabLeft >> return (not ld)
            Focusable _ fromRight -> writeIORef wref fromRight >> return False
            _ -> return True

          _ -> case foc of
            Focused _ _ _ onKey -> case onKey kEv of
              w'@(Continue _ _ _ (Focused _ _ _ _)) -> writeIORef wref w' >> return True
              w' -> writeIORef wref w' >> return True
            _ -> return True

mapWidgetFocus fwidget foc = case foc of
  NotFocusable -> NotFocusable
  Focusable fromLeft fromRight -> Focusable (fwidget fromLeft) (fwidget fromRight)
  Focused blur (tabLeft,ld) (tabRight,rd) key -> Focused (fwidget blur) (fwidget tabLeft, ld) (fwidget tabRight, rd) (fmap fwidget key)

mapGraphic fn w = case w of
  Finish z -> Finish z
  Continue out mouseOut anim foc -> let
    out' = fn $ (fmap.fmap) (id *** mapGraphic fn) out
    mouseOut' = fmap (mapGraphic fn) mouseOut
    anim' = (fmap.fmap) (mapGraphic fn) anim
    foc' = mapWidgetFocus (mapGraphic fn) foc
    in Continue out' mouseOut' anim' foc'

-- | A widget which just shows a constant graphic output.
graphicWidget :: (Functor f) => Maybe String -> f () -> Widget f a
graphicWidget murl g = Continue (const (murl, graphicWidget murl g) <$ g) Nothing Nothing NotFocusable

combineBeside :: GraphicTree a -> GraphicTree a -> GraphicTree a
combineBeside gt gt' =
  let bounds@(Rect l t w h) = graphicTreeBounds gt
      (Rect l' t' w' h') = graphicTreeBounds gt'
  in Branch bounds gt (Rect (l + w) t' w' h') (Offset (l + w - l', 0) gt')

-- | Combine two widgets side by side
beside :: Widget GraphicTree z -> Widget GraphicTree z -> Widget GraphicTree z
beside = zipW combineBeside

combineAbove :: GraphicTree a -> GraphicTree a -> GraphicTree a
combineAbove gt gt' =
  let bounds@(Rect l t w h) = graphicTreeBounds gt
      (Rect l' t' w' h') = graphicTreeBounds gt'
  in Branch bounds gt (Rect l' (t+h) w' h') (Offset (0, t + h - t') gt')

-- | Combine two widgets one above the other
above :: Widget GraphicTree z -> Widget GraphicTree z -> Widget GraphicTree z
above = zipW combineAbove
