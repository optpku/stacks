/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.GlobalSections.Terminal
public import ReasLib.CategoryTheory.Sites.Topos.Morphism

/-!
# Global sections and morphisms of topoi

This leaf owns the canonical terminal-object and global-sections comparisons
attached to a left-exact adjunction of type-valued sheaf topoi.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Inverse image along a morphism of topoi preserves the chosen terminal
type-valued sheaf. -/
noncomputable def inverseImageTerminalIso
    (f : MorphismOfTopoiIn JD JC) :
    f.inverseImage.obj
        (Sheaf.terminal JD Types.isTerminalPUnit : Sheaf JD (Type w)) ≅
      (Sheaf.terminal JC Types.isTerminalPUnit : Sheaf JC (Type w)) :=
  LeftExactAdjunction.inverseImageTerminalIso f
    (Sheaf.isTerminalTerminal JD Types.isTerminalPUnit)
    (Sheaf.isTerminalTerminal JC Types.isTerminalPUnit)

/-- Direct image followed by global sections is canonically isomorphic to
global sections on the source topos. -/
noncomputable def pushforwardCompΓIso
    (f : MorphismOfTopoiIn JD JC)
    [HasWeakSheafify JD (Type w)] [HasWeakSheafify JC (Type w)]
    [HasGlobalSectionsFunctor JD (Type w)] [HasGlobalSectionsFunctor JC (Type w)] :
    f.pushforward ⋙ Sheaf.Γ JD (Type w) ≅ Sheaf.Γ JC (Type w) :=
  NatIso.ofComponents (fun F ↦ Equiv.toIso <|
    (Sheaf.ΓObjEquivTerminalHom JD (f.pushforward.obj F)).trans <|
      (f.adjunction.homEquiv
        (Sheaf.terminal JD Types.isTerminalPUnit : Sheaf JD (Type w)) F).symm.trans <|
        (((f.inverseImageTerminalIso).homCongr (Iso.refl F)).trans
          (Sheaf.ΓObjEquivTerminalHom JC F).symm)) sorry

/-- Inverse image along a morphism of topoi commutes with the constant-sheaf
functor on types. -/
noncomputable def constantSheafCompInverseImageIso
    (f : MorphismOfTopoiIn JD JC)
    [HasWeakSheafify JD (Type w)] [HasWeakSheafify JC (Type w)]
    [HasGlobalSectionsFunctor JD (Type w)] [HasGlobalSectionsFunctor JC (Type w)] :
    constantSheaf JD (Type w) ⋙ f.inverseImage ≅ constantSheaf JC (Type w) :=
  Adjunction.leftAdjointUniq
    (((constantSheafΓAdj JD (Type w)).comp f.adjunction).ofNatIsoRight
      f.pushforwardCompΓIso)
    (constantSheafΓAdj JC (Type w))

end CategoryTheory.MorphismOfTopoiIn
