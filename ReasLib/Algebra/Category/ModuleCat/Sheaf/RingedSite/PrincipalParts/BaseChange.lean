module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange

/-!
# Base change for principal-parts sheaves

Principal-parts base change is first constructed sectionwise in the presheaf owner.  The generic
change-of-rings adjunction for module sheafification then supplies the canonical sheaf morphism.
This construction works on an arbitrary ringed site.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {phi : O₁ ⟶ O₂}
variable {phi' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}
variable {F : ringedSiteModuleCategory J O₂}
variable {F' : ringedSiteModuleCategory J O₂'}

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Tag 0G3W: the canonical base-change morphism between principal-parts sheaves on a ringed
site. -/
@[stacks 0G3W "principal-parts base change"]
noncomputable def map (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') (k : ℕ) :
    PrincipalParts.sheaf phi F k ⟶
      (restrictionAlong b).obj (PrincipalParts.sheaf phi' F' k) :=
  ModuleSheafification.mapToRestriction b
    (PresheafOfModules.PrincipalParts.BaseChange.map
      (a := a.hom) (φ := phi.hom) (φ' := phi'.hom) (β := b.hom)
      (sq.map (sheafToPresheaf J CommRingCat)) alpha.val k)

section AdjunctionSpec

variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Under the module-sheafification adjunction, the principal-parts base-change map is represented
by the sectionwise base-change map followed by the restricted target sheafification unit. -/
theorem homEquiv_map (sq : CommSq a phi phi' b)
    (alpha : F ⟶ (restrictionAlong b).obj F') (k : ℕ) :
    (moduleSheafificationAdjunction O₂).homEquiv
        (PrincipalParts.presheaf phi F k)
        ((restrictionAlong b).obj (PrincipalParts.sheaf phi' F' k))
        (map sq alpha k) =
      PresheafOfModules.PrincipalParts.BaseChange.map
          (a := a.hom) (φ := phi.hom) (φ' := phi'.hom) (β := b.hom)
          (sq.map (sheafToPresheaf J CommRingCat)) alpha.val k ≫
        (PresheafOfModules.restrictScalars (ringSheafMap b).hom).map
          ((moduleSheafificationUnit O₂').app
            (PrincipalParts.presheaf phi' F' k)) := sorry

end AdjunctionSpec

/-- Principal-parts base-change morphisms preserve composition of commutative ring squares and
compatible module-sheaf morphisms. -/
@[simp]
theorem map_comp
    {O₁'' O₂'' : Sheaf J CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {phi'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a phi phi' b) (sq' : CommSq a' phi' phi'' b')
    {F'' : ringedSiteModuleCategory J O₂''}
    (alpha : F ⟶ (restrictionAlong b).obj F')
    (alpha' : F' ⟶ (restrictionAlong b').obj F'') (k : ℕ) :
    map (CommSq.horiz_comp sq sq')
        (alpha ≫ (restrictionAlong b).map alpha') k =
      map sq alpha k ≫ (restrictionAlong b).map (map sq' alpha' k) := sorry

end Sheafification

end SheafOfModules.RingedSite.PrincipalParts.BaseChange
