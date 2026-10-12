/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Pairing
public import ReasLib.AlgebraicGeometry.Scheme.K0.PerfectComparison
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality

@[expose] public section

open AlgebraicGeometry CategoryTheory
open MonoidalClosed.Dual.Pairing
open Scheme.Hom
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

/-- The canonical comparison from the degree-zero tensor-dual presentation of
`Hⁱ(X, ω_X ⊗ᴸ Eᵛ)` to `Extⁱ(E, ω_X)`. -/
noncomputable def perfectTensorExtComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace) (i : ℤ) :
    DerivedExt.value f (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
      ((properDualizingComplex f).obj⟦i⟧ ⊗ MonoidalClosed.dual E.obj) 0 →ₗ[k]
        DerivedExt.value f
          ((@coherentBoundedToDerivedQCoh X
            (LocallyOfFiniteType.isLocallyNoetherian f)).obj
              ((@Scheme.K0.perfectToBoundedCoherent X
                (FiniteType.isNoetherian f)).obj E)).obj
          (properDualizingComplex f).obj i where
  toFun ξ := MonoidalClosed.Dual.homComparison E.obj
    ((properDualizingComplex f).obj⟦i⟧)
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ)
  map_add' := sorry
  map_smul' := sorry

/-- The tensor-dual comparison is bijective because a perfect complex is right-dualizable. -/
theorem perfectTensorExtComparison_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace) (i : ℤ) :
    Function.Bijective (perfectTensorExtComparison f E i) := sorry

/-- Composing the tensor-to-`Ext` comparison with a class from `E` is cup product followed
by the dual evaluation map, in the pointwise form of
`MonoidalClosed.Dual.Pairing.commSq_apply`. -/
theorem perfectTensorExtComparison_comp
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace) (i : ℤ)
    (ξ : DerivedExt.value f (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
      ((properDualizingComplex f).obj⟦i⟧ ⊗ MonoidalClosed.dual E.obj) 0)
    (η : 𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace) ⟶ E.obj) :
    η ≫ perfectTensorExtComparison f E i ξ =
      right ((properDualizingComplex f).obj⟦i⟧) E.obj
        (top ((properDualizingComplex f).obj⟦i⟧) E.obj
          ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm ξ, η)) := sorry

/-- The tensor-dual trace pairing, obtained by transporting `pairingWith` along
the canonical tensor-to-`Ext` comparison in its first argument. -/
noncomputable def perfectPairingWith
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace) (i : ℤ) :=
  let K :=
    (@coherentBoundedToDerivedQCoh X
      (LocallyOfFiniteType.isLocallyNoetherian f)).obj
        ((@Scheme.K0.perfectToBoundedCoherent X
          (FiniteType.isNoetherian f)).obj E)
  (pairingWith e f i K).compl₁₂
    (perfectTensorExtComparison f E i) LinearMap.id

/-- For a perfect complex, the trace pairing on
`Hⁱ(X, ω_X ⊗ᴸ Eᵛ) × H⁻ⁱ(X, E)` is perfect in every degree. -/
instance pairingWith_isPerfPair_of_perfect
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace) (i : ℤ) :
    LinearMap.IsPerfPair (perfectPairingWith e f E i) := sorry

/-- Evaluating the transported pairing gives the trace of the cup product followed by
the dual evaluation map; `MonoidalClosed.Dual.Pairing.commSq_apply` identifies this with
the displayed `homComparison`, and `pairingWith_trace` supplies the trace formula. -/
theorem perfectPairingWith_apply
    {k : Type u} [Field k] {X : Scheme.{u}}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (e : fieldObject k ≅ ModuleCat.of k k)
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (E : @RingedSpace.ModuleDerived.Perfect X.toRingedSpace) (i : ℤ)
    (ξ : DerivedExt.value f (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
      ((properDualizingComplex f).obj⟦i⟧ ⊗ MonoidalClosed.dual E.obj) 0)
    (η : cohomologyOverField f
      ((@coherentBoundedToDerivedQCoh X
        (LocallyOfFiniteType.isLocallyNoetherian f)).obj
          ((@Scheme.K0.perfectToBoundedCoherent X
            (FiniteType.isNoetherian f)).obj E)) (-i)) :
    perfectPairingWith e f E i ξ η =
      traceWith e f
        (cohomologyOverFieldMap f
          (ShiftedHom.sourceShiftEquiv
            ((@coherentBoundedToDerivedQCoh X
              (LocallyOfFiniteType.isLocallyNoetherian f)).obj
                ((@Scheme.K0.perfectToBoundedCoherent X
                  (FiniteType.isNoetherian f)).obj E))
            (properDualizingComplex f) i
            (ambientExtLift f i
              ((@coherentBoundedToDerivedQCoh X
                (LocallyOfFiniteType.isLocallyNoetherian f)).obj
                  ((@Scheme.K0.perfectToBoundedCoherent X
                    (FiniteType.isNoetherian f)).obj E))
              (perfectTensorExtComparison f E i ξ))) 0
          ((cohomologyNegShiftIso f i
            ((@coherentBoundedToDerivedQCoh X
              (LocallyOfFiniteType.isLocallyNoetherian f)).obj
                ((@Scheme.K0.perfectToBoundedCoherent X
                  (FiniteType.isNoetherian f)).obj E))).inv η)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
