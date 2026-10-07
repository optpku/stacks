module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.CanonicalExtensionBaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/- Lemma 52.16.9 (1): flat affine base change preserves canonical extension of a coherent
formal module from the inverse-image open to the ambient affine scheme. -/
@[stacks 0EIS] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_flatBaseChange :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {A' : Type u} [CommRing A'] [Algebra A A'] [Module.Flat A A']
    (S : AffineAlgebraizationSetup A)
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
    (h_extends : CanonicallyExtends S F),
    CanonicallyExtendsTo (S.baseChangeIdealSheaf A')
      (sectionsModuleProObject (S.baseChangeOpen A') (pullbackU.obj F)))

/- Lemma 52.16.9 (2): the pullback of a chosen canonical extension from
Lemma 52.16.8 realizes the canonical extension after flat affine base change. -/
@[stacks 0EIS] #check
  (AlgebraicGeometry.Scheme.CoherentFormalModules.canonicalExtension_flatBaseChange :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {A' : Type u} [CommRing A'] [Algebra A A'] [Module.Flat A A']
    (S : AffineAlgebraizationSetup A)
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
      sectionsProObject S F),
    Nonempty
      ((moduleProFunctor (S.baseChangeIdealSheaf A')).obj (pullbackX.obj G) ≅
        sectionsModuleProObject (S.baseChangeOpen A') (pullbackU.obj F)))

end AlgebraicGeometry.Scheme.CoherentFormalModules
