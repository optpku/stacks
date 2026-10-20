module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm
import Mathlib.Tactic.CrossRefAttribute

/-!
# Norms of morphisms of invertible modules

This file owns the norm morphism between Picard representatives and its fiberwise zero-locus
criterion.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ)

/-- For a finite morphism admitting a degree-`d` norm, every morphism of invertible modules
induces a morphism between the corresponding Picard-norm representatives. Its residue-fiber map
is zero at `y` exactly when the original residue-fiber map is zero at some point over `y`. -/
@[stacks 0BCZ]
theorem exists_picardNormMap_zeroAt_iff
    [IsFinite π]
    (hnorm : ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N) :
    ∃ normπ : X.PicardGroup →+ Y.PicardGroup,
      (∀ (𝒩 : Y.Modules) [MonoidalCategory.isInvertibleObject 𝒩],
        normπ (Scheme.Hom.picardPullbackClass π 𝒩) =
          d • Scheme.Modules.picardClass 𝒩) ∧
        ∀ (ℒ ℒ' : X.Modules) [MonoidalCategory.isInvertibleObject ℒ]
          [MonoidalCategory.isInvertibleObject ℒ'] (φ : ℒ ⟶ ℒ'),
          ∃ normφ :
            Scheme.PicardGroup.repr (normπ (Scheme.Modules.picardClass ℒ)) ⟶
              Scheme.PicardGroup.repr (normπ (Scheme.Modules.picardClass ℒ')),
            ∀ y : Y,
              ((∃ x : {x : X // π.base x = y}, Scheme.Modules.fiberMap φ x.1 = 0) ↔
                Scheme.Modules.fiberMap normφ y = 0) := sorry

end AlgebraicGeometry.Scheme
