/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Global generating sections under base change

Global generation of quasicoherent scheme modules is detected by faithfully flat affine base
change.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A A' : Type u} [CommRing A] [CommRing A']
variable {X : Scheme.{u}}

/-- Global generation of a quasicoherent module on a scheme over an affine base is preserved and
reflected by faithfully flat base change. -/
theorem isGloballyGenerated_iff_baseChangeModule_of_faithfullyFlat
    (f : X ⟶ Spec (CommRingCat.of A))
    (φ : A →+* A') (hff : φ.FaithfullyFlat)
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    SheafOfModules.IsGloballyGenerated ℱ ↔
      SheafOfModules.IsGloballyGenerated
        (Scheme.Modules.baseChangeModule f (Spec.map (CommRingCat.ofHom φ)) ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
