/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ModuleProRealization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Pullback

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {A' : Type u} [CommRing A'] [Algebra A A'] [Module.Flat A A']

/-- Flat affine base change preserves canonical extension of a coherent formal module
from the inverse-image open to the ambient affine scheme. -/
theorem canonicallyExtends_flatBaseChange (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (pullbackX : CoherentFormalModules S.X
        (Scheme.idealSheafDataOfIdealOnSpec S.I) ⥤
      CoherentFormalModules (S.baseChangeSpec A') (S.baseChangeIdealSheaf A'))
    (h_pullbackX : Scheme.IsCoherentFormalModulesPullbackFunctor (S.baseChangeMap A')
      (Scheme.idealSheafDataOfIdealOnSpec S.I) pullbackX)
    (pullbackU : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) ⥤
      CoherentFormalModules (S.baseChangeOpen A').toScheme
        (((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι).comap
          (S.baseChangeOpenMap A')))
    (h_pullbackU : Scheme.IsCoherentFormalModulesPullbackFunctor (S.baseChangeOpenMap A')
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) pullbackU)
    (h_extends : CanonicallyExtends S F) :
    CanonicallyExtendsTo (S.baseChangeIdealSheaf A')
      (sectionsModuleProObject (S.baseChangeOpen A') (pullbackU.obj F)) := sorry

/-- The pullback of a coherent formal module realizing the global-section pro-object
realizes the global-section pro-object after flat affine base change. -/
theorem canonicalExtension_flatBaseChange (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι))
    (pullbackX : CoherentFormalModules S.X
        (Scheme.idealSheafDataOfIdealOnSpec S.I) ⥤
      CoherentFormalModules (S.baseChangeSpec A') (S.baseChangeIdealSheaf A'))
    (h_pullbackX : Scheme.IsCoherentFormalModulesPullbackFunctor (S.baseChangeMap A')
      (Scheme.idealSheafDataOfIdealOnSpec S.I) pullbackX)
    (pullbackU : CoherentFormalModules S.U.toScheme
        ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) ⥤
      CoherentFormalModules (S.baseChangeOpen A').toScheme
        (((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι).comap
          (S.baseChangeOpenMap A')))
    (h_pullbackU : Scheme.IsCoherentFormalModulesPullbackFunctor (S.baseChangeOpenMap A')
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) pullbackU)
    (G : CoherentFormalModules S.X (Scheme.idealSheafDataOfIdealOnSpec S.I))
    (e : (proFunctor (Scheme.idealSheafDataOfIdealOnSpec S.I)).obj G ≅
      sectionsProObject S F) :
    Nonempty
      ((moduleProFunctor (S.baseChangeIdealSheaf A')).obj (pullbackX.obj G) ≅
        sectionsModuleProObject (S.baseChangeOpen A') (pullbackU.obj F)) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
