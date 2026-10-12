/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_37_4_Smooth

/-!
# Descent of syntomicity, smoothness, and étaleness along surjective morphisms

If `f` is a surjective and syntomic (resp. smooth, resp. étale) morphism of
algebraic spaces, and `f ≫ q` is syntomic (resp. smooth, resp. étale), then `q`
is syntomic (resp. smooth, resp. étale).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Syntomic

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
syntomicity descends from `p` to `q` along a surjective syntomic morphism `f`. -/
theorem of_comp_eq_of_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Syntomic f] [Syntomic p] (hcomm : f ≫ q = p) :
    Syntomic q := sorry

end Syntomic

namespace Smooth

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
smoothness descends from `p` to `q` along a surjective smooth morphism `f`. -/
theorem of_comp_eq_of_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Smooth f] [Smooth p] (hcomm : f ≫ q = p) :
    Smooth q := sorry

end Smooth

namespace Etale

/-- In a commutative triangle `f ≫ q = p` of algebraic spaces over `S`,
étaleness descends from `p` to `q` along a surjective étale morphism `f`. -/
theorem of_comp_eq_of_surjective {S : Scheme.{u}} {X Y B : AlgebraicSpace S}
    (f : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    [Surjective f] [Etale f] [Etale p] (hcomm : f ≫ q = p) :
    Etale q := sorry

end Etale

end AlgebraicGeometry.AlgebraicSpace
