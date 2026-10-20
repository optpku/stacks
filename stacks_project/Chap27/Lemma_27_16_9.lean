module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Presentation
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory
open scoped AlgebraicGeometry

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel : Type (u + 1))

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.degreeZeroRing :
    AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u} → CommRingCat.{u})

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.proj :
    AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u} → AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.specZero :
    AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u} → AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.toSpecZero :
    ∀ D : AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u},
      AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.proj D ⟶
        AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.specZero D)

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.specBase :
    AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u} → AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.baseToZero :
    ∀ D : AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u},
      D.baseRing ⟶ AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.degreeZeroRing D)

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.toSpecBase :
    ∀ D : AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u},
      AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.proj D ⟶
        AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.specBase D)

#check (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.isSeparated_toSpecBase :
    ∀ D : AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.{u},
      AlgebraicGeometry.IsSeparated
        (AlgebraicGeometry.Scheme.Hom.AbsoluteProjModel.toSpecBase D))

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjAffineChartAt :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) →
      SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u}
        (AlgebraicGeometry.Scheme.schemeCommRingSheaf S) → S → Type (u + 1))

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjAffineChartAt.modelMorphism :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u}
        (AlgebraicGeometry.Scheme.schemeCommRingSheaf S)} {s : S}
      (C : AlgebraicGeometry.Scheme.Hom.RelativeProjAffineChartAt p 𝒜 s),
        (p ⁻¹ᵁ (C.baseOpen : S.Opens)).toScheme ⟶ C.affineAlgebra.specBase)

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjAffineChartAt.modelMorphism_eq :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u}
        (AlgebraicGeometry.Scheme.schemeCommRingSheaf S)} {s : S}
      (C : AlgebraicGeometry.Scheme.Hom.RelativeProjAffineChartAt p 𝒜 s),
        C.modelMorphism =
          AlgebraicGeometry.morphismRestrict p (C.baseOpen : S.Opens) ≫ C.targetIso.hom)

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjAffineChartAt.isSeparated_restrict :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      {𝒜 : SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u}
        (AlgebraicGeometry.Scheme.schemeCommRingSheaf S)} {s : S}
      (C : AlgebraicGeometry.Scheme.Hom.RelativeProjAffineChartAt p 𝒜 s),
        AlgebraicGeometry.IsSeparated
          (AlgebraicGeometry.morphismRestrict p (C.baseOpen : S.Opens)))

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) → Type (u + 1))

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.degreePiece :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S},
      AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p → ℕ → S.Modules)

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.degreePiece_isQuasicoherent :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p) (d : ℕ),
        (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.degreePiece P d).IsQuasicoherent)

#check (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.iSup_affineChart_eq_top :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S}
      (P : AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p),
        ⨆ s : S, ((P.affineChart s).baseOpen : S.Opens) = ⊤)

/- Lemma 27.16.9: a morphism presented as a relative projective spectrum is separated. -/
@[stacks 01O2] #check (AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation.isSeparated :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} {p : X ⟶ S},
      AlgebraicGeometry.Scheme.Hom.RelativeProjPresentation p →
        AlgebraicGeometry.IsSeparated p)
