/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Over.Derived.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/-!
# Lemma 21.21.1

Lemma 21.21.1 (0EZ0) is the source-facing cartesian specialization of the reusable slice-site
derived base-change API.  The comparison is defined for a merely commutative square; the
`IsPullback` hypothesis is used only by `baseChangeIso` and `baseChangeAppIso` to expose its
invertibility.  The chapter file therefore owns no K-injective model, mate construction, or
derived-category transport helper.
-/

/- Lemma 21.21.1 (0EZ0): for a cartesian square
`X' ⟶ X`
`↓     ↓`
`Y' ⟶ Y`
in a site `𝒞`, the inverse image along `Y' ⟶ Y` commutes with the derived direct image along
`X ⟶ Y`; equivalently, the canonical map
`Rj_{X/Y,*} ⋙ j_{Y'/Y}^{-1} ⟶ j_{X'/X}^{-1} ⋙ Rj_{X'/Y',*}`
is an isomorphism. -/
@[stacks 0EZ0 "cartesian derived base-change isomorphism"]
#check @CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.iso

#check @CategoryTheory.GrothendieckTopology.Derived.Over.Pullback.squareIso
#check @CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.map
#check @CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.map_isMap
#check @CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.app
#check @CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.app_spec
#check @CategoryTheory.GrothendieckTopology.Derived.Over.BaseChange.appIso

end
