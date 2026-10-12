/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.ClosedPoints
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

#check PuncturedSpectrum.point
#check PuncturedSpectrum.point_val
#check PuncturedSpectrum.closedPoints_scheme_eq_empty_of_specializes

/- Example 26.11.9: in every universe there is a nonempty scheme with no closed points. -/
@[stacks 01IY] #check PuncturedSpectrum.exists_nonempty_scheme_without_closed_points

end AlgebraicGeometry
