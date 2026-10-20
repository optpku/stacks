module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.AffineSite
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticClosure

/-!
# Quasi-coherent derived objects on a category fibred in groupoids

`QC(𝒳)` is the comparison-map full subcategory `QC(𝒳_affine, 𝒪)` of derived
modules on the chaotic affine site with its restricted structure sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open CategoryTheory.ModulesOnCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- The comparison-map quasi-coherence property on derived modules over the
chaotic structure sheaf of `𝒳_affine`. -/
abbrev qcProperty : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) :=
  Chaotic.isQuasiCoherent.{u + 1, u, u} (affineStructureSheaf X)

/-- `qcProperty X` is the canonical comparison-map quasi-coherence property on
the chaotic affine site. -/
theorem qcProperty_eq :
    qcProperty X =
      Chaotic.isQuasiCoherent.{u + 1, u, u} (affineStructureSheaf X) :=
  sorry

/-- The triangulated category `QC(𝒳)` of quasi-coherent objects in the derived
category of `𝒳`. -/
abbrev QC := Chaotic.QC.{u + 1, u, u} (affineStructureSheaf X)

/-- `QC X` is the canonical quasi-coherent derived category of the chaotic affine
site with its restricted structure sheaf. -/
theorem QC_eq : QC X = Chaotic.QC.{u + 1, u, u} (affineStructureSheaf X) :=
  sorry

/-- A derived module lies in `qcProperty X` if and only if every canonical
comparison map associated to a morphism of `𝒳_affine` is an isomorphism. -/
theorem mem_QC_iff
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) :
    qcProperty X K ↔
      ∀ ⦃U V : affineSite X⦄ (f : U ⟶ V),
        IsIso ((chaoticComparison.{u + 1, u, u} (affineStructureSheaf X) f).app K) :=
  sorry

namespace QC

/-- The forgetful inclusion `QC(𝒳) ⥤ D(𝒳_affine, 𝒪)`. -/
abbrev inclusion :
    QC X ⥤
      RingedSite.Hom.ModuleDerived.{u + 1}
        (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X)) :=
  (qcProperty X).ι

/-- The inclusion of a quasi-coherent derived object is the underlying derived
module. -/
theorem inclusion_obj (K : QC X) : (inclusion X).obj K = K.obj :=
  sorry

end QC

end AlgebraicGeometry.GroupoidsOver
