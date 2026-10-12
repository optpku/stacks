/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Galois.Functoriality

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

universe u v u' v' w

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
variable {C' : Type u'} [Category.{v'} C'] [GaloisCategory C']
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
variable (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']

/- Lemma 58.3.11 -/
@[stacks 0BN5]
#check (CategoryTheory.PreGaloisCategory.existsIso_comp_fiber F F' :
  ∀ (H : C ⥤ C'), exactFunctor C C' H → Nonempty (H ⋙ F' ≅ F))

#check (CategoryTheory.PreGaloisCategory.inducedMonoidHom F F' :
  ∀ (H : C ⥤ C'), (H ⋙ F' ≅ F) → Aut F' →* Aut F)

#check (CategoryTheory.PreGaloisCategory.inducedContinuousHomCore F F' :
  ∀ (H : C ⥤ C'), (H ⋙ F' ≅ F) → ContinuousMonoidHom (Aut F') (Aut F))

#check (CategoryTheory.PreGaloisCategory.inducedContinuousHom_apply F F' :
  ∀ (H : C ⥤ C') (t : H ⋙ F' ≅ F) (g : Aut F'),
    inducedContinuousHomCore F F' H t g =
      t.conjAut (((whiskeringLeft C C' FintypeCat).obj H).mapAut F' g))

#check (CategoryTheory.PreGaloisCategory.inducedContinuousHomCore_catCommSq F F' :
  ∀ (H : C ⥤ C') (t : H ⋙ F' ≅ F),
    CatCommSq H (functorToContAction F) (functorToContAction F')
      (ContAction.res FintypeCat (inducedContinuousHomCore F F' H t)))

#check (CategoryTheory.PreGaloisCategory.inducedContinuousHomCore_conj F F' :
  ∀ (H : C ⥤ C') (t t' : H ⋙ F' ≅ F), ∃ g : Aut F, ∀ σ : Aut F',
    inducedContinuousHomCore F F' H t' σ =
      g * inducedContinuousHomCore F F' H t σ * g⁻¹)

#check (CategoryTheory.PreGaloisCategory.functorOfContinuousHomCore F F' :
  ContinuousMonoidHom (Aut F') (Aut F) → C ⥤ C')

#check (CategoryTheory.PreGaloisCategory.forgetContAction (Aut F) :
  ContAction FintypeCat.{w} (Aut F) ⥤ FintypeCat.{w})

#check (CategoryTheory.PreGaloisCategory.fiberIso_functorToContAction F' :
  F' ≅ functorToContAction F' ⋙ forgetContAction (Aut F'))

#check (CategoryTheory.PreGaloisCategory.res_comp_forgetContAction F F' :
  ∀ h : ContinuousMonoidHom (Aut F') (Aut F),
    ContAction.res FintypeCat h ⋙ forgetContAction (Aut F') ≅ forgetContAction (Aut F))

#check (CategoryTheory.PreGaloisCategory.functorToContAction_comp_forget F :
  functorToContAction F ⋙ forgetContAction (Aut F) ≅ F)

#check (CategoryTheory.PreGaloisCategory.inv_comp_fiberIso_functorToContAction F' :
  (functorToContAction F').inv ⋙ F' ≅ forgetContAction (Aut F'))

#check (CategoryTheory.PreGaloisCategory.fiberIsoOfContinuousHom F F' :
  ∀ h : ContinuousMonoidHom (Aut F') (Aut F),
    functorOfContinuousHomCore F F' h ⋙ F' ≅ F)

#check (CategoryTheory.PreGaloisCategory.functorOfContinuousHom_exact F F' :
  ∀ h : ContinuousMonoidHom (Aut F') (Aut F),
    exactFunctor C C' (functorOfContinuousHomCore F F' h))

#check (CategoryTheory.PreGaloisCategory.functorOfContinuousHom_induced F F' :
  ∀ h : ContinuousMonoidHom (Aut F') (Aut F),
    inducedContinuousHomCore F F' (functorOfContinuousHomCore F F' h)
      (fiberIsoOfContinuousHom F F' h) = h)

#check (CategoryTheory.PreGaloisCategory.inducedContinuousHom F F' :
  ∀ (H : C ⥤ C'), exactFunctor C C' H → (H ⋙ F' ≅ F) →
    ContinuousMonoidHom (Aut F') (Aut F))

#check (CategoryTheory.PreGaloisCategory.inducedContinuousHom_catCommSq F F' :
  ∀ (H : C ⥤ C') (h_exact : exactFunctor C C' H) (t : H ⋙ F' ≅ F),
    CatCommSq H (functorToContAction F) (functorToContAction F')
      (ContAction.res FintypeCat (inducedContinuousHom F F' H h_exact t)))

#check (CategoryTheory.PreGaloisCategory.inducedContinuousHom_conj F F' :
  ∀ (H : C ⥤ C') (h_exact : exactFunctor C C' H) (t t' : H ⋙ F' ≅ F),
    ∃ g : Aut F, ∀ σ : Aut F',
      inducedContinuousHom F F' H h_exact t' σ =
        g * inducedContinuousHom F F' H h_exact t σ * g⁻¹)

#check (CategoryTheory.PreGaloisCategory.functorOfContinuousHom F F' :
  ContinuousMonoidHom (Aut F') (Aut F) → C ⥤ C')

#check (CategoryTheory.PreGaloisCategory.functorOfContinuousHom_exact_ofHom F F' :
  ∀ h : ContinuousMonoidHom (Aut F') (Aut F),
    exactFunctor C C' (functorOfContinuousHom F F' h))

#check (CategoryTheory.PreGaloisCategory.functorOfContinuousHom_induced_ofHom F F' :
  ∀ h : ContinuousMonoidHom (Aut F') (Aut F),
    inducedContinuousHom F F' (functorOfContinuousHom F F' h)
      (functorOfContinuousHom_exact_ofHom F F' h) (fiberIsoOfContinuousHom F F' h) = h)
