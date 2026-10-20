module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Global sections through the terminal sheaf

This leaf identifies global sections of a type-valued sheaf with morphisms
from the canonical terminal sheaf.  It packages the terminal choice once, so
downstream arguments do not expose `PUnit` or repeat sheafification transport.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C]

/-- The constant sheaf on a singleton type is canonically isomorphic to the
terminal type-valued sheaf. -/
noncomputable def constantPUnitIsoTerminal
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)] :
    (constantSheaf J (Type w)).obj PUnit.{w + 1} ≅
      Sheaf.terminal J Types.isTerminalPUnit := by
  simpa [constantSheaf, Sheaf.terminal] using
    (sheafificationIso (Sheaf.terminal J Types.isTerminalPUnit)).symm

/-- Global sections are canonically equivalent to morphisms from the chosen
terminal sheaf. -/
noncomputable def ΓObjEquivTerminalHom
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (F : Sheaf J (Type w)) :
    (Sheaf.Γ J (Type w)).obj F ≃ (Sheaf.terminal J Types.isTerminalPUnit ⟶ F) :=
  (Sheaf.ΓObjEquivHom J F PUnit.{w + 1}).trans
    ((constantPUnitIsoTerminal J).homCongr (Iso.refl F))

/-- The terminal-sheaf description of global sections is natural in the sheaf. -/
theorem ΓObjEquivTerminalHom_naturality
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)]
    {F G : Sheaf J (Type w)} (η : F ⟶ G) (x : (Sheaf.Γ J (Type w)).obj F) :
    ΓObjEquivTerminalHom J G ((Sheaf.Γ J (Type w)).map η x) =
      ΓObjEquivTerminalHom J F x ≫ η := sorry

/-- The inverse terminal-sheaf description of global sections is natural in
the sheaf. -/
theorem ΓObjEquivTerminalHom_naturality_symm
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)]
    {F G : Sheaf J (Type w)} (η : F ⟶ G)
    (τ : Sheaf.terminal J Types.isTerminalPUnit ⟶ F) :
    (ΓObjEquivTerminalHom J G).symm (τ ≫ η) =
      (Sheaf.Γ J (Type w)).map η ((ΓObjEquivTerminalHom J F).symm τ) := sorry

/-- Evaluating the terminal-sheaf morphism associated to a global section at
the unique point recovers the canonical restriction map. -/
theorem ΓObjEquivTerminalHom_app_eq_ΓRes
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] (F : Sheaf J (Type w)) (U : C)
    (x : (Sheaf.Γ J (Type w)).obj F) :
    (ΓObjEquivTerminalHom J F x).hom.app (op U) PUnit.unit = Sheaf.ΓRes F (op U) x := sorry

/-- After the standard universe lift, global sections are naturally the
covariant Hom functor represented by the chosen terminal sheaf. -/
noncomputable def ΓNatIsoCoyonedaTerminal
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [HasGlobalSectionsFunctor J (Type w)] :
    Sheaf.Γ J (Type w) ⋙ uliftFunctor.{u} ≅
      coyoneda.obj
        (op (Sheaf.terminal J Types.isTerminalPUnit : Sheaf J (Type w))) :=
  NatIso.ofComponents (fun F ↦ Equiv.toIso {
    toFun := fun x ↦ ΓObjEquivTerminalHom J F x.down
    invFun := fun y ↦ ULift.up ((ΓObjEquivTerminalHom J F).symm y)
    left_inv := sorry
    right_inv := sorry
  }) sorry

end CategoryTheory.Sheaf
