module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Monoidal.Mon
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Azumaya algebras of scheme modules

Étale-local endomorphism algebras of finite locally free positive-rank modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CategoryTheory.MonObj
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}}

/-- The internal endomorphism object of a scheme module is a monoid object, with unit and
multiplication given by the closed-category identity and composition maps. -/
noncomputable instance instMonObjInternalHomEnd (F : S.Modules) :
    MonObj (internalHom F F) where
  one := MonoidalClosed.id F
  mul := MonoidalClosed.comp F F F
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

/-- Pullback of a monoid object in scheme modules along a morphism of schemes. -/
noncomputable instance instMonObjPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (A : Y.Modules)
    [MonObj A] : MonObj ((pullback f).obj A) where
  one := (pullbackUnitIso f).inv ≫ (pullback f).map η[A]
  mul := (pullbackTensorIso f A A).inv ≫ (pullback f).map μ[A]
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry

/-- An Azumaya `𝒪_S`-algebra is a monoid object in `S.Modules` that is étale-locally isomorphic,
as a monoid object, to the internal endomorphism algebra of a finite locally free module of
positive fiber rank. -/
class IsAzumaya (A : S.Modules) [MonObj A] : Prop where
  exists_etale_endomorphism :
    ∃ (𝒰 : S.Cover.{u} Scheme.etalePrecoverage) (F : ∀ i, (𝒰.X i).Modules),
      (∀ i, IsFiniteLocallyFree (F i)) ∧
        (∀ i, ∀ x : 𝒰.X i, 0 < fiberFinrank (F i) x) ∧
          ∀ i, ∃ e : (pullback (𝒰.f i)).obj A ≅ internalHom (F i) (F i),
            IsMonHom e.hom

/-- Internal endomorphism algebras of finite locally free positive-rank modules are Azumaya. -/
theorem isAzumaya_internalHomEnd (F : S.Modules) [IsFiniteLocallyFree F]
    (hF : ∀ x : S, 0 < fiberFinrank F x) :
    IsAzumaya (internalHom F F) := sorry

/-- The structure sheaf, viewed as a scheme module, is finite locally free. -/
instance instIsFiniteLocallyFree_tensorUnit : IsFiniteLocallyFree (𝟙_ S.Modules) := sorry

/-- Fibers of the structure sheaf have positive rank. -/
theorem fiberFinrank_tensorUnit_pos (x : S) :
    0 < fiberFinrank (𝟙_ S.Modules) x := sorry

/-- The internal endomorphism algebra of the structure sheaf is Azumaya. -/
noncomputable instance instIsAzumayaInternalHomEnd_tensorUnit :
    IsAzumaya (internalHom (𝟙_ S.Modules) (𝟙_ S.Modules)) :=
  isAzumaya_internalHomEnd (𝟙_ S.Modules) fiberFinrank_tensorUnit_pos

/-- An `𝒪_S`-algebra is Azumaya if and only if it is étale-locally a positive-rank internal
endomorphism algebra. -/
theorem IsAzumaya.iff_exists_etale_endomorphism (A : S.Modules) [MonObj A] :
    IsAzumaya A ↔
      ∃ (𝒰 : S.Cover.{u} Scheme.etalePrecoverage) (F : ∀ i, (𝒰.X i).Modules),
        (∀ i, IsFiniteLocallyFree (F i)) ∧
          (∀ i, ∀ x : 𝒰.X i, 0 < fiberFinrank (F i) x) ∧
            ∀ i, ∃ e : (pullback (𝒰.f i)).obj A ≅ internalHom (F i) (F i),
              IsMonHom e.hom := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Tensor products of Azumaya algebras are Azumaya. -/
instance isAzumaya_tensor (A B : S.Modules) [MonObj A] [MonObj B] [IsAzumaya A] [IsAzumaya B] :
    IsAzumaya (A ⊗ B) := sorry

end AlgebraicGeometry.Scheme
