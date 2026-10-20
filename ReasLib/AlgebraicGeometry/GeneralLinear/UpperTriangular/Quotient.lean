/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.Row
public import ReasLib.AlgebraicGeometry.GeneralLinear.UpperTriangular.Action
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical

/-!
# The quotient of `GL₂` by its upper-triangular subgroup

This file constructs the comparison from the quotient sheaf to the sheaf represented by the
projective line.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GLTwo.UpperTriangular

/-- The second-row projectivization respects the structure morphisms to `Spec(k)`. -/
theorem secondRow_over (k : Type u) [CommRing k] :
    GeneralLinear.Row.toProjectiveSpace k 1 (1 : Fin 2) ≫
        (ProjectiveSpace.schemeOver k 1).hom =
      (GeneralLinear.groupScheme k (GLTwo.index)).X.hom := sorry

/-- The second-row projectivization regarded as a morphism over `Spec(k)`. -/
def secondRow (k : Type u) [CommRing k] :
    (GeneralLinear.groupScheme k (GLTwo.index)).X ⟶ ProjectiveSpace.schemeOver k 1 :=
  Over.homMk (GeneralLinear.Row.toProjectiveSpace k 1 (1 : Fin 2)) (secondRow_over k)

/-- The concrete quotient map: invert in `GL₂`, then projectivize the second row. -/
def quotientMap (k : Type u) [CommRing k] :
    (relation k).U ⟶ ProjectiveSpace.schemeOver k 1 :=
  ι[GeneralLinear.schemeOver k (GLTwo.index)] ≫ secondRow k

/-- The quotient map is invariant under the source and target maps of the relation. -/
theorem quotientMap_invariant (k : Type u) [CommRing k] :
    (relation k).toPreRelation.t ≫ quotientMap k =
      (relation k).toPreRelation.s ≫ quotientMap k := sorry

/-- Composition with the quotient map identifies generalized points related by the action
groupoid. -/
theorem quotientDesc_respects (k : Type u) [CommRing k]
    {T : Over (Spec (CommRingCat.of k))} {x y : T ⟶ (relation k).U}
    (hxy : (relation k).toPreRelation.pointRel T x y) :
    x ≫ quotientMap k = y ≫ quotientMap k := sorry

/-- The map from objectwise quotient classes to projective-line-valued points. -/
def quotientDescApp (k : Type u) [CommRing k]
    {T : Over (Spec (CommRingCat.of k))} :
    Quot ((relation k).toPreRelation.pointRel T) →
      (T ⟶ ProjectiveSpace.schemeOver k 1) :=
  Quot.lift (fun x ↦ x ≫ quotientMap k)
    (fun _ _ hxy ↦ quotientDesc_respects k hxy)

/-- The objectwise quotient map to projective-line-valued points is natural. -/
theorem quotientDesc_naturality (k : Type u) [CommRing k]
    {T T' : (Over (Spec (CommRingCat.of k)))ᵒᵖ} (f : T ⟶ T') :
    (relation k).toPreRelation.quotientPresheaf.map f ≫
        TypeCat.ofHom (quotientDescApp k) =
      TypeCat.ofHom (quotientDescApp k) ≫
        (yoneda.obj (ProjectiveSpace.schemeOver k 1)).map f := sorry

/-- The natural map from the quotient presheaf to the projective-line representable presheaf. -/
def quotientPresheafDesc (k : Type u) [CommRing k] :
    (relation k).toPreRelation.quotientPresheaf ⟶
      yoneda.obj (ProjectiveSpace.schemeOver k 1) where
  app _ := TypeCat.ofHom (quotientDescApp k)
  naturality {_ _} f := quotientDesc_naturality k f

/-- The comparison from the quotient sheaf to the sheaf represented by `ℙ¹`. -/
def quotientComparison (k : Type u) [CommRing k] (τ : StandardTopology) :
    (relation k).toPreRelation.quotientSheaf
        (τ.overTopology (Spec (CommRingCat.of k))) ⟶
      (τ.overTopology (Spec (CommRingCat.of k))).uliftYoneda.{u + 1}.obj
        (ProjectiveSpace.schemeOver k 1) :=
  (sheafificationAdjunction (τ.overTopology (Spec (CommRingCat.of k)))
      (Type (u + 1))).homEquiv
      ((relation k).toPreRelation.quotientPresheaf ⋙ uliftFunctor.{u + 1, u})
      ((τ.overTopology (Spec (CommRingCat.of k))).uliftYoneda.{u + 1}.obj
        (ProjectiveSpace.schemeOver k 1)) |>.symm
    (Functor.whiskerRight (quotientPresheafDesc k) uliftFunctor.{u + 1, u})

/-- Precomposing the quotient comparison with the quotient map gives the represented
projective quotient map. -/
theorem quotientComparison_quotientMap (k : Type u) [CommRing k]
    (τ : StandardTopology) :
    (relation k).toPreRelation.quotientMap
        (τ.overTopology (Spec (CommRingCat.of k))) ≫ quotientComparison k τ =
      (τ.overTopology (Spec (CommRingCat.of k))).uliftYoneda.map (quotientMap k) := sorry

/-- In the Zariski topology, the upper-triangular quotient of `GL₂` is represented by the
projective line. -/
@[instance]
theorem quotientComparison_zariski_isIso (k : Type u) [Field k] :
    IsIso (quotientComparison k .zariski) := sorry

/-- In the étale topology, the upper-triangular quotient of `GL₂` is represented by the
projective line. -/
@[instance]
theorem quotientComparison_etale_isIso (k : Type u) [Field k] :
    IsIso (quotientComparison k .etale) := sorry

/-- In the fppf topology, the upper-triangular quotient of `GL₂` is represented by the
projective line. -/
@[instance]
theorem quotientComparison_fppf_isIso (k : Type u) [Field k] :
    IsIso (quotientComparison k .fppf) := sorry

end AlgebraicGeometry.GLTwo.UpperTriangular
