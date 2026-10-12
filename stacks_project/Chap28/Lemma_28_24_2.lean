/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Torsion
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The ideal-sheaf subobject of `𝒪_X` represented by ideal sheaf data `I`. -/
noncomputable abbrev idealSheafSubobject (I : X.IdealSheafData) :
    Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  I.toSubobject

/- Lemma 28.24.2 (1): if `I` is a finite type quasi-coherent ideal sheaf on a scheme `X` and
`ℱ` is a quasi-coherent `𝒪_X`-module, then the subsheaf of sections annihilated by `I` is
quasi-coherent. -/
@[stacks 01PO] #check
  (AlgebraicGeometry.Scheme.Modules.idealTorsionSubsheaf_isQuasicoherent :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (I : X.IdealSheafData)
      [((Subobject.underlying.obj
        (AlgebraicGeometry.Scheme.Modules.idealSheafSubobject I) : X.Modules).IsFiniteType)],
      (AlgebraicGeometry.Scheme.Modules.idealTorsionSubsheaf I ℱ).IsQuasicoherent)

/- Lemma 28.24.2 (2): on an affine open, the image of the inclusion is the set of sections
annihilated by every section of the ideal. -/
@[stacks 01PO] #check
  (AlgebraicGeometry.Scheme.Modules.range_idealTorsionSubsheafι_app_eq_affine_annihilatedSections :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (I : X.IdealSheafData)
      [((Subobject.underlying.obj
        (AlgebraicGeometry.Scheme.Modules.idealSheafSubobject I) : X.Modules).IsFiniteType)]
      (U : X.affineOpens),
      Set.range (((AlgebraicGeometry.Scheme.Modules.idealTorsionSubsheafι
        I ℱ).val.app (Opposite.op U.1)).hom) =
        {s : Γ(ℱ, U.1) | ∀ a : Γ(X, U.1), a ∈ I.ideal U → a • s = 0})

/- Lemma 28.24.2 (3): at a point, the image of the stalk inclusion is the set of stalk sections
annihilated by every element of the stalk ideal. -/
@[stacks 01PO] #check
  (AlgebraicGeometry.Scheme.Modules.range_idealTorsionSubsheafι_stalk_eq_annihilatedStalkSections :
    ∀ {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (I : X.IdealSheafData)
      [((Subobject.underlying.obj
        (AlgebraicGeometry.Scheme.Modules.idealSheafSubobject I) : X.Modules).IsFiniteType)]
      (x : X),
      Set.range ((RingedSpace.moduleStalkHom x
        (AlgebraicGeometry.Scheme.Modules.idealTorsionSubsheafι I ℱ)).hom) =
        {s : RingedSpace.stalkModuleCat ℱ x |
          ∀ a : X.presheaf.stalk x,
            a ∈ RingedSpace.idealSheafStalkIdeal I.toSubobject x → a • s = 0})

end AlgebraicGeometry.Scheme.Modules
