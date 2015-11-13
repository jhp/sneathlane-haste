{-# LANGUAGE KindSignatures, RankNTypes, GADTs, OverloadedStrings #-}

module SneathLane.BasicWidgets where

import Control.Applicative (Applicative(..), liftA2)
import Control.Monad (mplus, when)
import Data.Monoid ((<>))
import Data.Functor ((<$))
import Data.Maybe (fromMaybe)
import Control.Arrow ((***))

import SneathLane.Graphics
import SneathLane.Widget

import System.IO.Unsafe (unsafePerformIO)

import Haste (writeLog, catJSStr, toJSString, fromJSStr)

logging x y = unsafePerformIO (writeLog (show x) >> return y)

rectPath ps w h r = QuadraticPath ps (0,r) [((0,0),(r,0)),
                                            ((w-r,0),(w-r,0)),
                                            ((w,0),(w,r)),
                                            ((w,h-r),(w,h-r)),
                                            ((w,h),(w-r,h)),
                                            ((r,h),(r,h)),
                                            ((0,h),(0,h-r)),
                                            ((0,r),(0,r))]

button textStyle label = blur
  where
    blur = Continue (output (RGBA 0 0 0 1)) Nothing Nothing (Focusable focus focus)

    focus = Continue (output (RGBA 0 1 0 1)) Nothing Nothing (Focused blur (blur, False) (blur, False) (\key -> case key of
                                                                                                               EvKeyDown 13 _ -> Finish () -- enter
                                                                                                               _ -> focus))

    output clr = handler <$ graphicList [rectPath (PathStyle (Just (clr, 2)) Nothing) (labelWidth + 10) 30 5,
                                             Text textStyle (5,5) label]

    handler (EvMouseDown _ LeftButton) = (Nothing, Finish ())
    handler _ = (Nothing, blur)

    labelWidth = measureText textStyle label

tabs textStyle ts n =
  let buttons = zipWith (\(label,_) n' -> button textStyle label >> return (Left n')) ts [0..]
      curr = fmap Right $ nextFrame $ snd $ ts !! n
  in do
    ret <- balancedFold beside buttons `above` curr
    case ret of
      Right (Finish z) -> Finish z
      Right w' -> tabs textStyle (zipWith (\(label,w) n' -> if n' == n then (label, w') else (label, w)) ts [0..]) n
      Left n' ->
        let (Continue out _ _ _) = curr
            (Rect _ _ _ h) = graphicTreeBounds out
        in tabs textStyle (zipWith (\(label,w) n -> (label, if n == n' then slideToHeight h 0.2 w else w)) ts [0..]) n'

slideToHeight initialHeight duration (Finish z) = Finish z

slideToHeight initialHeight duration (Continue out mouseOut anim foc) =
    let (Rect x y w h) = graphicTreeBounds out
        anim' = fromMaybe (\tm -> Continue out mouseOut Nothing foc) anim
        anim'' tm = let w' = anim' tm
                    in if tm > duration
                       then w'
                       else slideToHeight (initialHeight + (tm/duration)*(h - initialHeight)) (duration - tm) w'

        out' = Clip (Rect x y w initialHeight) out
        mouseOut' = fmap (slideToHeight initialHeight duration) mouseOut
        foc' = mapWidgetFocus (slideToHeight initialHeight duration) foc

    in Continue out' mouseOut' (Just anim'') foc'

nextFrame widget = case widget of
  Finish z -> Finish (Finish z)
  Continue out mouseOut anim foc ->
    let out' = (fmap . fmap) (\(murl, w) -> (murl, Finish w)) out
        mouseOut' = fmap Finish mouseOut
        anim' = (fmap . fmap) Finish anim
        foc' = mapWidgetFocus Finish foc
    in Continue out' mouseOut' anim' foc'

textInput ww ts txt focused = Continue out Nothing Nothing foc
  where
    out = const (Nothing, textInput ww ts txt True) <$ graphicList [
      rectPath (PathStyle (Just (if focused then RGBA 0 0 1 1 else RGBA 0 0 0 1, 1)) Nothing) ww (fromIntegral $ ts_lineHeight ts + 6) 5,
      Text ts (5,3) txt
      ]

    foc = if focused
          then Focused blur (blur, False) (blur, False) keys
          else Focusable focus focus

    keys = (\key -> case key of
              EvKeyDown 8 _ -> Finish (toJSString $ reverse $ drop 1 $ reverse $ fromJSStr txt, False)
              EvKeyDown 13 _ -> Finish (txt, True)
              EvKeyInput str -> Finish (catJSStr "" [txt, str], False)
              _ -> textInput ww ts txt focused)

    blur = textInput ww ts txt False
    focus = textInput ww ts txt True

autoComplete ts fcomps txt focused =
  let comps = fcomps txt
      ww = maximum $ map (measureText ts) (txt:map fst comps)
      ti = textInput (ww + 10) ts txt focused
      wi = balancedFold above (ti : map showComp comps)
      showComp comp = graphicWidget Nothing
                      (graphicList [
                           rectPath (PathStyle (Just (RGBA 0.4 0.4 0.4 1, 1)) (Just $ RGBA 0.9 0.9 0.9 1)) (ww + 10) (fromIntegral $ ts_lineHeight ts) 0,
                           Text ts (5,0) (fst comp)])
  in do
    (txt', finish) <- wi
    case finish of
      True -> if null comps
              then autoComplete ts fcomps txt True
              else return (snd $ head comps)
      False -> if txt' /= "" && null (fcomps txt')
               then autoComplete ts fcomps txt True
               else autoComplete ts fcomps txt' True

simpleFocus fw keys = focus
  where
    focus = fw $ Focused blur (blur, False) (blur, False) keys
    blur = fw $ Focusable focus focus
