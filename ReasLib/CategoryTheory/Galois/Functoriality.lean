/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Action.Finite.Exact
public import ReasLib.CategoryTheory.Galois.Equivalence
public import ReasLib.CategoryTheory.Galois.InducedHom

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

universe u v u' v' w uG

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
variable {C' : Type u'} [Category.{v'} C'] [GaloisCategory C']
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
variable (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']

/-- The functor associated to a continuous homomorphism `h : Aut F' →ₜ* Aut F`,
obtained by restriction of scalars and the Galois-category equivalences. -/
noncomputable def functorOfContinuousHomCore (h : ContinuousMonoidHom (Aut F') (Aut F)) :
    C ⥤ C' :=
  functorToContAction F ⋙ ContAction.res FintypeCat h ⋙ (functorToContAction F').inv

/-- The underlying finite-set functor of finite continuous `G`-sets. -/
def forgetContAction (G : Type uG) [Monoid G] [TopologicalSpace G] :
    ContAction FintypeCat.{w} G ⥤ FintypeCat.{w} :=
  ObjectProperty.ι _ ⋙ forget₂ _ FintypeCat

/-- The fibre functor `F'` is naturally isomorphic to the underlying-set functor
of its finite continuous action realization. -/
def fiberIso_functorToContAction :
    F' ≅ functorToContAction F' ⋙ forgetContAction (Aut F') :=
  NatIso.ofComponents (fun X ↦ Iso.refl (F'.obj X)) fun _ ↦ sorry

/-- Restriction of scalars preserves the underlying finite set. -/
def res_comp_forgetContAction (h : ContinuousMonoidHom (Aut F') (Aut F)) :
    ContAction.res FintypeCat h ⋙ forgetContAction (Aut F') ≅
      forgetContAction (Aut F) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ sorry

/-- The action realization of `F` followed by the underlying-set functor recovers `F`. -/
def functorToContAction_comp_forget :
    functorToContAction F ⋙ forgetContAction (Aut F) ≅ F :=
  NatIso.ofComponents (fun X ↦ Iso.refl (F.obj X)) fun _ ↦ sorry

/-- The inverse action equivalence identifies `F'` with the underlying-set functor. -/
noncomputable def inv_comp_fiberIso_functorToContAction :
    (functorToContAction F').inv ⋙ F' ≅ forgetContAction (Aut F') :=
  isoWhiskerLeft (functorToContAction F').inv (fiberIso_functorToContAction F') ≪≫
    Equivalence.invFunIdAssoc (functorToContAction F').asEquivalence (forgetContAction (Aut F'))

/-- The fibre comparison associated to a continuous homomorphism. -/
noncomputable def fiberIsoOfContinuousHom (h : ContinuousMonoidHom (Aut F') (Aut F)) :
    functorOfContinuousHomCore F F' h ⋙ F' ≅ F :=
  (associator (functorToContAction F ⋙ ContAction.res FintypeCat h)
      (functorToContAction F').inv F').symm ≪≫
    isoWhiskerLeft (functorToContAction F ⋙ ContAction.res FintypeCat h)
      (inv_comp_fiberIso_functorToContAction F') ≪≫
    associator (functorToContAction F) (ContAction.res FintypeCat h)
      (forgetContAction (Aut F')) ≪≫
    isoWhiskerLeft (functorToContAction F) (res_comp_forgetContAction F F' h) ≪≫
    functorToContAction_comp_forget F

/-- The converse functor associated to a continuous homomorphism is exact. -/
theorem functorOfContinuousHom_exact (h : ContinuousMonoidHom (Aut F') (Aut F)) :
    exactFunctor C C' (functorOfContinuousHomCore F F' h) :=
  sorry

/-- The converse functor and its fibre comparison recover the original homomorphism. -/
theorem functorOfContinuousHom_induced (h : ContinuousMonoidHom (Aut F') (Aut F)) :
    inducedContinuousHomCore F F' (functorOfContinuousHomCore F F' h)
      (fiberIsoOfContinuousHom F F' h) = h :=
  sorry

/-- An exact functor between Galois categories admits a fibre comparison isomorphism. -/
theorem existsIso_comp_fiber (H : C ⥤ C') (h_exact : exactFunctor C C' H) :
    Nonempty (H ⋙ F' ≅ F) :=
  sorry

/-- The continuous homomorphism induced by an exact functor and a fibre comparison. -/
def inducedContinuousHom (H : C ⥤ C') (h_exact : exactFunctor C C' H) (t : H ⋙ F' ≅ F) :
    ContinuousMonoidHom (Aut F') (Aut F) :=
  inducedContinuousHomCore F F' H t

/-- The exact-functor-induced homomorphism gives a comparison square
between the finite continuous action realizations. -/
@[implicit_reducible]
def inducedContinuousHom_catCommSq (H : C ⥤ C') (h_exact : exactFunctor C C' H)
    (t : H ⋙ F' ≅ F) :
    CatCommSq H (functorToContAction F) (functorToContAction F')
      (ContAction.res FintypeCat (inducedContinuousHom F F' H h_exact t)) :=
  inducedContinuousHomCore_catCommSq F F' H t

/-- The exact-functor-induced homomorphism is independent of the fibre comparison
up to an inner automorphism of `Aut F`. -/
theorem inducedContinuousHom_conj (H : C ⥤ C') (h_exact : exactFunctor C C' H)
    (t t' : H ⋙ F' ≅ F) :
    ∃ g : Aut F, ∀ σ : Aut F',
      inducedContinuousHom F F' H h_exact t' σ =
        g * inducedContinuousHom F F' H h_exact t σ * g⁻¹ :=
  sorry

/-- The canonical converse functor associated to a continuous homomorphism. -/
noncomputable def functorOfContinuousHom (h : ContinuousMonoidHom (Aut F') (Aut F)) : C ⥤ C' :=
  functorOfContinuousHomCore F F' h

/-- The canonical converse functor is exact. -/
theorem functorOfContinuousHom_exact_ofHom (h : ContinuousMonoidHom (Aut F') (Aut F)) :
    exactFunctor C C' (functorOfContinuousHom F F' h) :=
  sorry

/-- The canonical converse functor and its fibre comparison recover the given homomorphism. -/
theorem functorOfContinuousHom_induced_ofHom (h : ContinuousMonoidHom (Aut F') (Aut F)) :
    inducedContinuousHom F F' (functorOfContinuousHom F F' h)
      (functorOfContinuousHom_exact_ofHom F F' h)
      (fiberIsoOfContinuousHom F F' h) = h :=
  sorry

end CategoryTheory.PreGaloisCategory
