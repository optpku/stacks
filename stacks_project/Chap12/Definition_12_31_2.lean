module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
import StacksCheckRecall

@[expose] public section

/- Definition 12.31.2 [02N0]: a sequential inverse system is Mittag-Leffler when, at each
target stage, the images of sufficiently late transition maps stabilize. The generalized owner
`SequentialInverseSystem.IsMittagLeffler` requires only images in the ambient category. -/
@[stacks 02N0] #check @CategoryTheory.SequentialInverseSystem.IsMittagLeffler
