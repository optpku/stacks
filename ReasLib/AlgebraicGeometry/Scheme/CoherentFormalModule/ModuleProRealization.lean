module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtension
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Ambient-module pro-realizations of coherent formal modules

Coherent formal modules are realized in the pro-category of all module sheaves. Unlike
the quasicoherent realization, this construction does not require the ambient scheme to be
Noetherian.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- The pro-object of ambient module sheaves represented by the stages of a coherent formal
module. -/
noncomputable def moduleProFunctor {X : Scheme.{u}} (I : X.IdealSheafData) :
    CoherentFormalModules X I ⥤ Pro X.Modules :=
  (IsCoherentFormalModuleSystem I).ι ⋙
    (Functor.whiskeringRight ℕᵒᵖ
      (RingedSpace.Coh X.toRingedSpace) X.Modules).obj
        (SheafOfModules.isCoherent X.ringCatSheaf).ι ⋙
    Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ

/-- The object represented by `moduleProFunctor I` is the ambient-module inverse system of
the stages of the coherent formal module. -/
theorem moduleProFunctor_obj {X : Scheme.{u}} (I : X.IdealSheafData)
    (F : CoherentFormalModules X I) :
    (moduleProFunctor I).obj F =
      (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj
        (F.obj ⋙ (SheafOfModules.isCoherent X.ringCatSheaf).ι) := sorry

/-- The ambient-module pro-object on `Spec A` represented by the sheaves associated to
`H⁰(U, Fₙ)`. -/
noncomputable def sectionsModuleProObject {A : Type u} [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) {J : U.toScheme.IdealSheafData}
    (F : CoherentFormalModules U.toScheme J) :
    Pro (Spec (CommRingCat.of A)).Modules :=
  (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj
    (F.obj ⋙ (SheafOfModules.isCoherent U.toScheme.ringCatSheaf).ι ⋙
      Scheme.Hom.globalSectionsFunctor U.ι ⋙
      (@AlgebraicGeometry.tildeEquiv (CommRingCat.of A)).functor ⋙
      Scheme.QCoh.inclusion (Spec (CommRingCat.of A)))

/-- The defining `H⁰`-and-associated-sheaf presentation of
`sectionsModuleProObject U F`. -/
theorem sectionsModuleProObject_eq {A : Type u} [CommRing A]
    (U : (Spec (CommRingCat.of A)).Opens) {J : U.toScheme.IdealSheafData}
    (F : CoherentFormalModules U.toScheme J) :
    sectionsModuleProObject U F =
      (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj
        (F.obj ⋙ (SheafOfModules.isCoherent U.toScheme.ringCatSheaf).ι ⋙
          Scheme.Hom.globalSectionsFunctor U.ι ⋙
          (@AlgebraicGeometry.tildeEquiv (CommRingCat.of A)).functor ⋙
          Scheme.QCoh.inclusion (Spec (CommRingCat.of A))) := sorry

/-- An ambient-module pro-object canonically extends along `I` when it lies in the essential
image of `moduleProFunctor I`. -/
def CanonicallyExtendsTo {X : Scheme.{u}} (I : X.IdealSheafData)
    (P : Pro X.Modules) : Prop :=
  (moduleProFunctor I).essImage P

/-- An ambient-module pro-object canonically extends exactly when it is isomorphic to the
pro-realization of a coherent formal module. -/
theorem canonicallyExtendsTo_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (P : Pro X.Modules) :
    CanonicallyExtendsTo I P ↔
      ∃ G : CoherentFormalModules X I,
        Nonempty ((moduleProFunctor I).obj G ≅ P) := sorry

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Forgetting quasicoherence carries the canonical-extension property to the
ambient-module realization. -/
theorem CanonicallyExtends.toModules (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    CanonicallyExtends S F →
      CanonicallyExtendsTo (idealSheafDataOfIdealOnSpec S.I)
        (sectionsModuleProObject S.U F) := sorry

/-- The ambient-module pro-object obtained by pushing forward the stages of a formal module. -/
noncomputable def pushforwardProObject {X : Scheme.{u}} (U : X.Opens)
    {J : U.toScheme.IdealSheafData} (F : CoherentFormalModules U.toScheme J) :
    Pro X.Modules :=
  (Pro.lim.{u + 1, u, 0, 0} ℕᵒᵖ).obj
    (F.obj ⋙ (SheafOfModules.isCoherent U.toScheme.ringCatSheaf).ι ⋙
      Scheme.Modules.pushforward U.ι)

end AlgebraicGeometry.Scheme.CoherentFormalModules
