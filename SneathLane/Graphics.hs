{-# LANGUAGE OverloadedStrings #-}

module SneathLane.Graphics (
  -- * Type
  Graphic(..),

  -- * Functions
  drawGraphic,
  graphicBounds,
  inGraphic,

  inRect,
  measureText,
  pixelRatio,

  -- * Auxiliary Types
  Point,
  Rect(..),
  Color(..),
  PathStyle(..),
  TextStyle(..),

  -- * Re-exported
  Canvas,
  Picture,
  render,
  getCanvas
  ) where

import Data.Maybe (fromJust, isJust)
import Control.Monad (when)

import Haste (JSString, toJSString, catJSStr)
import Haste.Foreign (ffi)
import Haste.Graphics.Canvas (Canvas, Picture, Ctx, createCanvas, getCanvas, withContext, render)

import System.IO.Unsafe (unsafePerformIO)

-- | A point, represented as (x,y); following browser convention, positive x points right and positive y points downward.
type Point = (Double, Double)

-- | A rectangle, stored as left, top, width, height
data Rect = Rect Double Double Double Double

inRect :: Point -> Rect -> Bool
inRect (x,y) (Rect l t w h) = x >= l && x < l + w && y >= t && y < t + h

-- | An RGBA color, each number should be between 0 and 1. Future version will include gradients.
data Color = RGBA Double Double Double Double

colorToString :: Color -> JSString
colorToString (RGBA r g b a) =
  catJSStr "" ["rgba(",
               intToJSString $ floor $ 255 * r, ",",
               intToJSString $ floor $ 255 * g, ",",
               intToJSString $ floor $ 255 * b, ",",
               toJSString a, ")"]

-- | Determines how a path is drawn. Stroke includes width as well as color.
data PathStyle = PathStyle {
      ps_stroke :: Maybe (Color, Double),
      ps_fill :: Maybe Color
}

-- | Determines how a text string is drawn to the canvas.
data TextStyle = TextStyle {
      ts_color :: Color,
      ts_size :: Int,
      ts_lineHeight :: Int,
      ts_italic :: Bool,
      ts_bold :: Bool,
      ts_font :: JSString
}

toFontString :: TextStyle -> JSString
toFontString ts = catJSStr "" [if ts_italic ts then "italic " else "",
                               if ts_bold ts then "bold " else "",
                               intToJSString $ floor (pixelRatio * fromIntegral (ts_size ts)), "px ",  --"px / ", toJSString $ ts_lineHeight ts, "px ",
                               ts_font ts]

-- | The Graphic type
data Graphic = QuadraticPath PathStyle Point [(Point, Point)] -- ^ A path made up of quadratic Bezier curves, start point + (control point, end point) list.
             | Text TextStyle Point JSString -- ^ Text string, point indicates top left of text bounding box
             | BlankGraphic Rect -- ^ Invisible graphic which takes up space. Useful for e.g. a spacer.



-- | Draw a graphic to a canvas, with the given point as the top left
drawGraphic :: Graphic -> Point -> Picture ()
drawGraphic (Text ts (x, y) str) (x',y') = withContext $ \ctx -> do
  jsFillStyle ctx (colorToString $ ts_color ts)
  jsFont ctx (toFontString ts)
  let bottom = 0.5 * fromIntegral (ts_size ts) + 0.5 * fromIntegral (ts_lineHeight ts)
  jsFillText ctx str (pixelRatio*(x+x')) (pixelRatio*(y+y'+bottom))

drawGraphic (QuadraticPath ps (x,y) comps) (x',y') = withContext $ \ctx -> do
  maybe (return ()) (\(clr, width) -> jsStrokeStyle ctx (colorToString clr) >> jsStrokeWidth ctx (pixelRatio*width)) (ps_stroke ps)
  maybe (return ()) (\clr -> jsFillStyle ctx (colorToString clr)) (ps_fill ps)

  jsBeginPath ctx
  jsMoveTo ctx (pixelRatio * (x + x')) (pixelRatio * (y + y'))
  mapM_
    (\((x1,y1),(x2,y2)) ->
      jsQuadraticCurveTo ctx (pixelRatio * (x' + x1)) (pixelRatio * (y' + y1)) (pixelRatio * (x' + x2)) (pixelRatio * (y' + y2)))
    comps

  when (isJust $ ps_stroke ps) (jsStroke ctx)
  when (isJust $ ps_fill ps) (jsFill ctx)

drawGraphic (BlankGraphic _) _ = return ()

-- | Find a rectangle that contains the entire graphic
graphicBounds :: Graphic -> Rect
graphicBounds (QuadraticPath ps (x,y) comps) =
  let (minX, minY, maxX, maxY) = foldl (\(ax,ay,zx,zy) ((x',y'),(x'',y'')) -> (min (min ax x') x'', min (min ay y') y'', max (max zx x') x'', max (max zy y') y'')) (x, y, x, y) comps
      sw = maybe 0 snd (ps_stroke ps)
  in Rect (minX-sw) (minY-sw) (2*sw + maxX - minX) (2*sw + maxY - minY)

graphicBounds (Text ts (x,y) str) = Rect x y (measureText ts str) (fromIntegral $ ts_lineHeight ts)

graphicBounds (BlankGraphic rct) = rct

-- | Determine if a point is inside a graphic.
--
-- A point is considered inside a text string if it is within the
-- rectangle defined by the line height and width of the text.
--
-- A point is considered inside a path if a ray from the point
-- directly to the left crosses the path an odd number of times. This
-- works as expected for closed non-intersecting paths.
inGraphic :: Point -> Graphic -> Bool
inGraphic pt g@(Text _ _ _) = pt `inRect` (graphicBounds g)

inGraphic pt (BlankGraphic rct) = pt `inRect` rct

inGraphic (x,y) (QuadraticPath _ pt comps) = odd $ length $ filter (< x) $ xCrossings pt comps y

xCrossings :: Point -> [(Point,Point)] -> Double -> [Double]
xCrossings _ [] _ = []

xCrossings (x,y) (((cx,cy), (ex,ey)) : comps) y' =
    let rest = xCrossings (ex,ey) comps y'
        (sx,sy) = (x - cx, y - cy)
        (ex',ey') = (ex - cx, ey - cy)
    in if sy + ey' == 0
       then let xs = map (\t -> cx + (1-t)*(1-t)*sx + t*t*ex') $ filter (\t -> t >= 0 && t <= 1) [-(y' - y)/(2*sy)] in xs ++ rest
       else let radicand = (sy*sy + (ey' + sy)*(y' - y)) / ((ey' + sy)*(ey' + sy))
            in if radicand <= 0
               then rest
               else let t0 = sy / (ey' + sy)
                        t1 = t0 + sqrt radicand
                        t2 = t0 - sqrt radicand
                        xs = map (\t -> cx + (1-t)*(1-t)*sx + t*t*ex') $ filter (\t -> t >= 0 && t <= 1) [t1, t2]
                    in xs ++ rest

-- Canvas FFI

jsQuadraticCurveTo :: Ctx -> Double -> Double -> Double -> Double -> IO ()
jsQuadraticCurveTo = ffi "(function(ctx, x1, y1, x2, y2) { ctx.quadraticCurveTo(x1,y1,x2,y2); })"

jsBeginPath :: Ctx -> IO ()
jsBeginPath = ffi "(function(ctx) { ctx.beginPath(); })"

jsStrokeStyle :: Ctx -> JSString -> IO ()
jsStrokeStyle = ffi "(function(ctx, str) { ctx.strokeStyle = str; })"

jsFillStyle :: Ctx -> JSString -> IO ()
jsFillStyle = ffi "(function(ctx, str) { ctx.fillStyle = str; })"

jsFont :: Ctx -> JSString -> IO ()
jsFont = ffi "(function(ctx, str) { ctx.font = str; })"

jsStroke :: Ctx -> IO ()
jsStroke = ffi "(function(ctx) { ctx.stroke(); })"

jsFill :: Ctx -> IO ()
jsFill = ffi "(function(ctx) { ctx.fill(); })"

jsMeasureText :: Ctx -> JSString -> IO Double
jsMeasureText = ffi "(function(ctx, str) { return ctx.measureText(str).width; })"

measureCanvas :: Canvas
measureCanvas = fromJust $ unsafePerformIO (createCanvas 1 1)

measureText :: TextStyle -> JSString -> Double
measureText textStyle text = (1/pixelRatio) * (unsafePerformIO $ render measureCanvas $ withContext (\ctx -> jsFont ctx (toFontString textStyle) >> jsMeasureText ctx text))

jsFillText :: Ctx -> JSString -> Double -> Double -> IO ()
jsFillText = ffi "(function(ctx, str, x, y) { return ctx.fillText(str, x, y); })"

jsStrokeWidth :: Ctx -> Double -> IO ()
jsStrokeWidth = ffi "(function(ctx, sw) { ctx.strokeWidth = sw; })"

jsMoveTo :: Ctx -> Double -> Double -> IO ()
jsMoveTo = ffi "(function(ctx, x, y) { return ctx.moveTo(x, y); })"

intToJSString :: Int -> JSString
intToJSString = toJSString

getPixelRatio :: IO Double
getPixelRatio = ffi "(function() { return window.devicePixelRatio; })"

pixelRatio :: Double
pixelRatio = unsafePerformIO $ getPixelRatio
