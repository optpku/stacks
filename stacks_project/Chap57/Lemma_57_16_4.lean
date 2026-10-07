module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import stacks_project.Chap57.Definition_57_15_1_Kernel
public import stacks_project.Chap57.Lemma_57_16_3

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/-- The fibre of a smooth proper morphism over a `k`-rational section `σ : Spec k ⟶ S`,
as the pullback `Y ×_S Spec k`. -/
noncomputable def FourierMukaiObject.fiberOver
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    FourierMukaiObject (Spec (.of k)) where
  scheme := pullback Y.hom σ
  hom := pullback.snd Y.hom σ
  smooth := sorry
  proper := sorry

/-- The constant family `Y_s ×_{Spec k} S` over `S`. -/
noncomputable def FourierMukaiObject.constantFamily
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    FourierMukaiObject S :=
  FourierMukaiObject.baseChange hS (FourierMukaiObject.fiberOver hS σ hσ Y)

/-- The structure morphism of the constant family is the base-change projection to `S`. -/
theorem FourierMukaiObject.constantFamily_hom
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    (FourierMukaiObject.constantFamily hS σ hσ Y).hom =
      pullback.fst hS (FourierMukaiObject.fiberOver hS σ hσ Y).hom := sorry

/-- The fibre of the constant family at the image of `σ` is isomorphic to `Y_s`. -/
theorem FourierMukaiObject.constantFamily_fiber
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    IsIsomorphic
      ((FourierMukaiObject.constantFamily hS σ hσ Y).hom.fiber (σ (closedPoint k)))
      (pullback Y.hom σ) := sorry

/-- The first projection of `Y_s ×_k Y_s` is compatible with the pullback square
defining the constant family. -/
theorem FourierMukaiObject.fiberSquare_fst_lift_condition
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    (pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
      pullback.fst Y.hom σ ≫ Y.hom) ≫ hS =
      pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
          (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom := sorry

/-- The map `Y_s ×_k Y_s ⟶ Y_s ×_{Spec k} S` induced by the first projection. -/
noncomputable def FourierMukaiObject.fiberSquareToConstantFamily
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    pullback (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ⟶
      (FourierMukaiObject.constantFamily hS σ hσ Y).scheme :=
  pullback.lift
    (pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
      pullback.fst Y.hom σ ≫ Y.hom)
    (pullback.fst (FourierMukaiObject.fiberOver hS σ hσ Y).hom
      (FourierMukaiObject.fiberOver hS σ hσ Y).hom)
    (FourierMukaiObject.fiberSquare_fst_lift_condition hS σ hσ Y)

/-- The two legs of `Y_s ×_k Y_s ⟶ (Y_s × S) ×_S Y` agree over `S`. -/
theorem FourierMukaiObject.fiberSquareToConstantProduct_condition
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    FourierMukaiObject.fiberSquareToConstantFamily hS σ hσ Y ≫
        (FourierMukaiObject.constantFamily hS σ hσ Y).hom =
      (pullback.snd (FourierMukaiObject.fiberOver hS σ hσ Y).hom
          (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
        pullback.fst Y.hom σ) ≫ Y.hom := sorry

/-- The comparison morphism `Y_s ×_k Y_s ⟶ (Y_s × S) ×_S Y` used to restrict kernels. -/
noncomputable def FourierMukaiObject.fiberSquareToConstantProduct
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S) :
    pullback (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ⟶
      pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom :=
  pullback.lift
    (FourierMukaiObject.fiberSquareToConstantFamily hS σ hσ Y)
    (pullback.snd (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom ≫
      pullback.fst Y.hom σ)
    (FourierMukaiObject.fiberSquareToConstantProduct_condition hS σ hσ Y)

/-- Derived restriction of a perfect kernel along the fibre-square comparison. -/
noncomputable def FourierMukaiObject.fiberSquarePullbackKernel
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.fiberOver hS σ hσ Y).hom
        (FourierMukaiObject.fiberOver hS σ hσ Y).hom).toRingedSpace :=
  (RingedSpace.modulePullbackPerfect
    (FourierMukaiObject.fiberSquareToConstantProduct hS σ hσ Y).toLRSHom.toShHom).obj K

/-- Restriction of `K` along `Y_s × Y_s ⟶ X ×_S Y` is the derived pullback of `K`. -/
theorem FourierMukaiObject.fiberSquarePullbackKernel_spec
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom).toRingedSpace) :
    FourierMukaiObject.fiberSquarePullbackKernel hS σ hσ Y K =
      (RingedSpace.modulePullbackPerfect
        (FourierMukaiObject.fiberSquareToConstantProduct hS σ hσ Y).toLRSHom.toShHom).obj K :=
  sorry

/-- An isomorphism of restricted families over an open `U` yields an isomorphism
of the underlying schemes. -/
theorem FourierMukaiObject.opens_restrict_isIso
    {S : Scheme.{u}} (Y X : FourierMukaiObject S) (U : S.Opens)
    (e : (FourierMukaiObject.baseChange U.ι Y).scheme ⟶
      (FourierMukaiObject.baseChange U.ι X).scheme)
    (he : e ≫ (FourierMukaiObject.baseChange U.ι X).hom =
      (FourierMukaiObject.baseChange U.ι Y).hom)
    [IsIso e] :
    Nonempty
      ((FourierMukaiObject.baseChange U.ι Y).scheme ≅
        (FourierMukaiObject.baseChange U.ι X).scheme) := sorry

/-- Lemma 57.16.4: if `Y → S` is smooth proper over a finite-type `k`-scheme with
`k`-rational point `s`, `X = Y_s × S` is the constant family, and a relative
Fourier--Mukai kernel `K` from `X` to `Y` restricts along
`Y_s ×_S Y_s ⟶ X ×_S Y` to the diagonal kernel `Δ_{Y_s/k,*} 𝒪_{Y_s}`, then `Y`
is isomorphic to that constant family over some open neighbourhood of `s`. -/
@[stacks 0G0R]
theorem exists_isIso_restriction_of_relativeEquivalenceKernel_fiber_diagonal
    {k : Type u} [Field k] {S : Scheme.{u}} (hS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType hS] (σ : Spec (.of k) ⟶ S) (hσ : σ ≫ hS = 𝟙 _)
    (s : S) (hs : s = σ (closedPoint k))
    (Y : FourierMukaiObject S)
    (K : @RingedSpace.ModuleDerived.Perfect
      (pullback (FourierMukaiObject.constantFamily hS σ hσ Y).hom Y.hom).toRingedSpace)
    [FourierMukaiObject.IsRelativeEquivalenceKernel K]
    (hK : IsIsomorphic
      (FourierMukaiObject.fiberSquarePullbackKernel hS σ hσ Y K)
      (FourierMukaiObject.diagonalKernel (FourierMukaiObject.fiberOver hS σ hσ Y))) :
    ∃ U : S.Opens, s ∈ U ∧ ∃
      e : (FourierMukaiObject.baseChange U.ι Y).scheme ⟶
        (FourierMukaiObject.baseChange U.ι
          (FourierMukaiObject.constantFamily hS σ hσ Y)).scheme,
      e ≫ (FourierMukaiObject.baseChange U.ι
            (FourierMukaiObject.constantFamily hS σ hσ Y)).hom =
          (FourierMukaiObject.baseChange U.ι Y).hom ∧
        IsIso e := sorry
