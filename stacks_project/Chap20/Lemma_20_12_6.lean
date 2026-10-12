/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Cohomology.Cech
import StacksCheckRecall

@[expose] public section

/- Lemma 20.12.6 (0A36): let `𝒰 : U = ⋃ᵢ Uᵢ` be an open covering and let `ℱ` be an
abelian sheaf.  If every restriction map from `ℱ(U)` to an arbitrary union of finite
intersections of the covering opens is surjective, then the positive-degree Čech cohomology
of `(𝒰, ℱ)` vanishes.  The reusable owners are the intrinsic finite-intersection predicate
and the short sheaf-level vanishing theorem in `ReasLib`; this file is only the labeled check.
-/

@[stacks 0A36 "unions of finite Cech intersections"]
#check @TopCat.Presheaf.Cech.IsUnionOfFiniteIntersections

@[stacks 0A36 "finite-intersection union inclusion"]
#check @TopCat.Presheaf.Cech.IsUnionOfFiniteIntersections.le_iSup

@[stacks 0A36 "positive-degree Cech vanishing from surjective restrictions"]
#check @TopCat.Sheaf.Cohomology.Cech.isZero_of_surjective_restrictions
