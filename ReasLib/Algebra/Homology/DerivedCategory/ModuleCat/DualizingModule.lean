module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.RingTheory.Normal.Local
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat

/-- A finite module over a Noetherian ring is dualizing when every shift of
its degree-zero derived complex is an intrinsic dualizing complex. -/
def IsDualizingModule {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : ModuleCat.{u} A) : Prop :=
  Module.Finite A ω ∧
    ∀ n : ℤ, DerivedCategory.IsDualizing ((ModuleCat.single0 ω)⟦n⟧)

/-- The finiteness-and-all-shifts characterization of an intrinsic dualizing module. -/
theorem isDualizingModule_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    (ω : ModuleCat.{u} A) :
    IsDualizingModule ω ↔
      Module.Finite A ω ∧
        ∀ n : ℤ,
          DerivedCategory.IsDualizing ((ModuleCat.single0 ω)⟦n⟧) := sorry

namespace IsDualizingModule

/-- Every integer shift of the degree-zero complex of a dualizing module is dualizing. -/
theorem shift {A : Type u} [CommRing A] [IsNoetherianRing A]
    {ω : ModuleCat.{u} A} (hω : IsDualizingModule ω) (n : ℤ) :
    DerivedCategory.IsDualizing ((ModuleCat.single0 ω)⟦n⟧) := sorry

/-- Over a two-dimensional Noetherian normal local ring, dualizing complexes and
dualizing modules exist simultaneously. -/
theorem existsComplex_iff_exists_of_normalLocalDomain
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]
    (h_dimension : ringKrullDim A = 2) :
    (∃ K : DerivedCategory (ModuleCat.{u} A), DerivedCategory.IsDualizing K) ↔
      ∃ ωA : ModuleCat.{u} A, IsDualizingModule ωA := sorry

end IsDualizingModule
end ModuleCat
