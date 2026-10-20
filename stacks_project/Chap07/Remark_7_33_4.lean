module

public import ReasLib.CategoryTheory.Sites.Point.Construction

import StacksCheckRecall

@[expose] public section

/-! [stacks 00YD]
Remark 7.33.4 is formalized by the reusable point-fiber criterion rather than a
chapter-specific bundled alias. -/
@[stacks 00YD] #check @CategoryTheory.GrothendieckTopology.Point.Fiber.IsPointFiber
#check @CategoryTheory.GrothendieckTopology.Point.Fiber.isPointFiber_of_point
