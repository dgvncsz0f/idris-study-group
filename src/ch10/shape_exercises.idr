module ShapeExercises

import Shape

area : Shape -> Double
area s with (shapeView s)
  area (triangle x y) | STriangle   = 0.5 * x * y
  area (rectangle x y) | SRectangle = x * y
  area (circle x) | SCircle         = pi * x * x
