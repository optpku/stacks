module

public import ReasLib.CategoryTheory.Sites.Point.Enough
import StacksCheckRecall

@[expose] public section

open CategoryTheory.GrothendieckTopology

/- Lemma 18.14.4 (05V3) (1): a conservative family of points detects exactness stalkwise. -/
@[stacks 05V3 "(1)"]
#check @PointFamily.exact_iff_stalkwise

/- Lemma 18.14.4 (05V3) (2): enough points detect exactness on all stalks. -/
@[stacks 05V3 "(2)"]
#check @HasEnoughPoints.exact_iff_stalkwise
