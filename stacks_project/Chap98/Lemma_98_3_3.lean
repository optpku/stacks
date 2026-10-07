module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.Lemma_98_3_3_Predeformation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibre products of predeformation categories

A 2-fibre product of categories fibered in groupoids over `(Sch/S)_fppf` induces a
fibre product of the associated predeformation categories at a finite-type field
over a locally Noetherian scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- Lemma 98.3.3: Let `S` be a locally Noetherian scheme, and let `W, X, Y, Z` be
categories fibered in groupoids over `(Sch/S)_fppf` forming a 2-fibre product
square. Let `k` be a finite-type field over `S` and let `w0` be an object of `W`
over `k`. Then the induced square of predeformation categories
`ℱ_{W, k, w0}`, `ℱ_{X, k, x0}`, `ℱ_{Z, k, z0}`, `ℱ_{Y, k, y0}` is a fibre
product of predeformation categories, where `x0`, `z0`, `y0` are the images of
`w0`. -/
@[stacks 07WL]
theorem mapCone_isBilimit {S : Scheme.{u}} [IsLocallyNoetherian S]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    {W X Y Z : GroupoidsOver S} (fX : X ⟶ Y) (gZ : Z ⟶ Y) (fW : W ⟶ X) (gW : W ⟶ Z)
    (sq : fW ≫ fX ≅ gW ≫ gZ) (w0 : W.p.Fiber (Over.mk kToS))
    (hW : Bicategory.PseudoPullbackCone.IsBilimit
      (⟨W, fW, gW, sq⟩ : Bicategory.PseudoPullbackCone fX gZ)) :
    (mapCone openImmersion kToS h_factor fX gZ fW gW sq w0).IsBilimit :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
