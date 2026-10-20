/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Scalar
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction.Derived.Coherence

/-!
# Derived Change of Scalars from the Base Ring

The canonical map from the base ring to a cochain differential graded algebra is compatible
with derived restriction and extension along every homomorphism of cochain DG algebras.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace CochainDGAlgebra.Hom.Derived

variable {R : Type u} [CommRing R]
variable {A B : CochainDGAlgebra.{u, u} R}

/-- Restriction along a cochain-DGA homomorphism followed by restriction to the base ring is
canonically isomorphic to direct restriction to the base ring. -/
noncomputable def restrictionCompFromBaseIso (f : A ⟶ B) :
    restriction.{u, u, u, u} f ⋙
        restriction.{u, u, u, u} (CochainDGAlgebra.Hom.fromBase A) ≅
      restriction.{u, u, u, u} (CochainDGAlgebra.Hom.fromBase B) :=
  (restrictionCompIso (CochainDGAlgebra.Hom.fromBase A) f :
      restriction.{u, u, u, u} f ⋙
          restriction.{u, u, u, u} (CochainDGAlgebra.Hom.fromBase A) ≅
        restriction.{u, u, u, u}
          (CochainDGAlgebra.Hom.comp f (CochainDGAlgebra.Hom.fromBase A))) ≪≫
    eqToIso (congrArg
      (fun g ↦ restriction.{u, u, u, u} g)
      (CochainDGAlgebra.Hom.comp_fromBase f))

/-- Extension from the base ring followed by extension along a cochain-DGA homomorphism is
canonically isomorphic to direct extension from the base ring. -/
noncomputable def extensionCompFromBaseIso (f : A ⟶ B) :
    extension.{u, u} (CochainDGAlgebra.Hom.fromBase A) ⋙
        extension.{u, u} f ≅
      extension.{u, u} (CochainDGAlgebra.Hom.fromBase B) :=
  (extensionCompIso (CochainDGAlgebra.Hom.fromBase A) f :
      extension.{u, u} (CochainDGAlgebra.Hom.fromBase A) ⋙
          extension.{u, u} f ≅
        extension.{u, u}
          (CochainDGAlgebra.Hom.comp f (CochainDGAlgebra.Hom.fromBase A))) ≪≫
    eqToIso (congrArg
      (fun g ↦ extension.{u, u} g)
      (CochainDGAlgebra.Hom.comp_fromBase f))

end CochainDGAlgebra.Hom.Derived
