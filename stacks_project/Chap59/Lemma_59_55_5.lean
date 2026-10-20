/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EtaleCohomology.CechDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsFinite f] [Surjective f] [(Arrow.mk f).HasCechNerve]
variable (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal Y.Etale]
variable [(siteAbelianSectionsFunctor Y.smallEtaleTopology (terminal Y.Etale)).Additive]
variable [∀ n : ℕ, HasSheafify (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ n : ℕ, Abelian (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ n : ℕ,
  HasInjectiveResolutions (Sheaf (finiteCechScheme f n).smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ n : ℕ, HasTerminal (finiteCechScheme f n).Etale]
variable [∀ n : ℕ,
  (siteAbelianSectionsFunctor (finiteCechScheme f n).smallEtaleTopology
    (terminal (finiteCechScheme f n).Etale)).Additive]

/- Lemma 59.55.5 (1): for a surjective finite morphism, the augmented Čech sheaf complex is exact. -/
@[stacks 09Z2] #check
  (AlgebraicGeometry.Scheme.Etale.finiteCechComplex_exact f F :
    (finiteCechComplex f F).Acyclic)

/- Lemma 59.55.5 (2): the finite Čech spectral sequence has the stated first page and abutment. -/
@[stacks 09Z2] #check
  (AlgebraicGeometry.Scheme.Etale.finiteCech_spectralSequence f F :
    ∃ (E : CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1)
      (pageOneIso : ∀ p q : ℕ,
        (E.page 1 le_rfl).X (p, q) ≅ finiteCech_pageOne f F p q),
      CohomologicalSpectralSequenceNat.FinitelyAbutsTo E (finiteCech_abutment F))

/- Lemma 59.55.5 (3): the finite Čech spectral sequence is functorial in the coefficient sheaf. -/
@[stacks 09Z2] #check
  (AlgebraicGeometry.Scheme.Etale.finiteCech_spectralSequence_functorial f :
    ∃ (E : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u} ⥤
      CohomologicalSpectralSequenceNat AddCommGrpCat.{u} 1)
      (pageOneIso : ∀ (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (p q : ℕ),
        ((E.obj F).page 1 le_rfl).X (p, q) ≅ finiteCech_pageOne f F p q)
      (pageOneNaturality : ∀ {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}}
        (α : F ⟶ G) (p q : ℕ),
        ((E.map α).hom 1 le_rfl).f (p, q) ≫ (pageOneIso G p q).hom =
          (pageOneIso F p q).hom ≫
            ((siteAbelianSectionsFunctor (finiteCechScheme f p).smallEtaleTopology
                (terminal (finiteCechScheme f p).Etale)).rightDerived q).map
              ((abelianInverseImage (finiteCechMap f p)).map α)),
      (∀ F, CohomologicalSpectralSequenceNat.FinitelyAbutsTo (E.obj F)
        (finiteCech_abutment F)))

end AlgebraicGeometry.Scheme.Etale
