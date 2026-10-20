/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Sections of counits for adjunctions into `Type`

When the left adjoint of an adjunction into `Type` preserves the terminal
object, every component of its counit has a canonical section.  This is the
small categorical core behind several point-of-a-topos constructions.
-/

@[expose] public section

open CategoryTheory Limits

universe u v w

noncomputable section

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C]
variable {L : C ⥤ Type w} {R : Type w ⥤ C}

/-- The endofunctor `R ⋙ L` sends the terminal type to the terminal type when
the left adjoint `L` preserves terminal objects. -/
@[stacks 05UX "terminal comparison for a Type-valued adjunction"]
noncomputable def counitTerminalIso (adj : L ⊣ R)
  [PreservesLimit (Functor.empty.{0} C) L] :
    (R ⋙ L).obj PUnit.{w + 1} ≅ PUnit.{w + 1} := by
  -- Local instance justification (instance diamond): Mathlib exposes the
  -- right-adjoint limit theorem as a lemma, and the transported empty-diagram
  -- preservation is specific to this terminal-object construction.
  letI : PreservesLimitsOfSize R := adj.rightAdjoint_preservesLimits
  letI : PreservesLimit (Functor.empty.{0} (Type w) ⋙ R) L :=
    preservesLimit_of_iso_diagram L (Functor.emptyExt (Functor.empty.{0} C) _)
  exact ((R ⋙ L).mapIso Types.terminalIso).symm ≪≫
    PreservesTerminal.iso (R ⋙ L) ≪≫ Types.terminalIso

/-- The canonical point of `(R ⋙ L).obj PUnit` obtained by terminality. -/
@[stacks 05UX "canonical terminal point for a Type-valued adjunction"]
noncomputable def counitTerminalPoint (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] :
    (R ⋙ L).obj PUnit.{w + 1} :=
  (counitTerminalIso adj).inv PUnit.unit

/-- The canonical natural section of the counit of an adjunction `L ⊣ R`
whose left adjoint preserves terminal objects. -/
@[stacks 05UX "canonical section of a Type-valued adjunction counit"]
noncomputable def counitSection (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] :
    𝟭 (Type w) ⟶ R ⋙ L where
  app E := ↾fun e ↦ (R ⋙ L).map (↾fun _ : PUnit.{w + 1} ↦ e) (counitTerminalPoint adj)
  naturality := sorry

/-- The canonical counit section splits the counit as a natural transformation. -/
@[stacks 05UX "counit section identity"]
theorem counitSection_comp (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] :
    counitSection adj ≫ adj.counit = 𝟙 _ := sorry

/-- The canonical section of the counit is a left inverse to its component. -/
@[stacks 05UX "componentwise counit section"]
theorem counit_leftInverse (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] (E : Type w) :
    Function.LeftInverse (adj.counit.app E) ((counitSection adj).app E) := sorry

/-- Every counit component of an adjunction into `Type` whose left adjoint
preserves the terminal object is split epic. -/
@[stacks 05UX "split-epi Type-valued counit"]
theorem counit_isSplitEpi (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] (E : Type w) :
    IsSplitEpi (adj.counit.app E) := sorry

/-- The right adjoint of an adjunction into `Type` is faithful when its left
adjoint preserves the terminal object. -/
@[stacks 05UX "faithful right adjoint from terminal preservation"]
theorem faithful_of_preservesTerminal (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] :
    R.Faithful := sorry

/-- The right adjoint of an adjunction into `Type` whose left adjoint
preserves the terminal object reflects monomorphisms. -/
@[stacks 05UX "mono reflection for a Type-valued right adjoint"]
theorem reflectsMonomorphisms_of_preservesTerminal (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] :
    R.ReflectsMonomorphisms := sorry

/-- The right adjoint of an adjunction into `Type` whose left adjoint
preserves the terminal object reflects epimorphisms. -/
@[stacks 05UX "epi reflection for a Type-valued right adjoint"]
theorem reflectsEpimorphisms_of_preservesTerminal (adj : L ⊣ R)
    [PreservesLimit (Functor.empty.{0} C) L] :
    R.ReflectsEpimorphisms := sorry

end CategoryTheory.Adjunction
