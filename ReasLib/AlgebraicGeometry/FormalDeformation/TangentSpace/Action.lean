module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Action
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.CategoryTheory.Cofibered.Fiber
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses

/-!
# Derivation action on tangent spaces

Pushforward along derivation-induced dual-number endomorphisms acts on the tangent
space of a predeformation category.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Functor

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

noncomputable section

/-- A residue-field derivation acts on the tangent space by the isomorphism-class map
of cofibered pushforward along its dual-number automorphism. -/
def derivationAction (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    (derivation : Derivation Λ k k) : tangentSpace p → tangentSpace p :=
  (pushforwardFiberFunctor p (cleavageOp p)
    (ArtinianLocalAlgCat.dualNumberAut derivation)).isoClassesMap

/-- Residue-field derivations act on the tangent space by cofibered pushforward along
their dual-number endomorphisms. -/
instance instAddAction_tangentSpace [IsPredeformationCategory p] :
    AddAction (Derivation Λ k k) (tangentSpace p) :=
  let operation : Derivation Λ k k → tangentSpace p → tangentSpace p := derivationAction p
  let laws : (∀ left right value,
      operation (left + right) value = operation left (operation right value)) ∧
      (∀ value, operation 0 value = value) := sorry
  { vadd := operation
    add_vadd := laws.1
    zero_vadd := laws.2 }

/-- The tangent-space action is the isomorphism-class map of pushforward along the
derivation-induced dual-number endomorphism. -/
theorem vadd_tangentSpace [IsPredeformationCategory p] (derivation : Derivation Λ k k)
    (value : tangentSpace p) :
    derivation +ᵥ value =
      (pushforwardFiberFunctor p (cleavageOp p)
        (ArtinianLocalAlgCat.dualNumberAut derivation)).isoClassesMap value := rfl

/-- The action on a represented tangent vector is the isomorphism class of the
cofibered pushforward of its fibre representative. -/
theorem derivationAction_mk (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    (derivation : Derivation Λ k k)
    (fiberObject : p.Fiber (ArtinianLocalAlgCat.dualNumber Λ k)) :
    derivationAction p derivation (tangentSpace.mk p fiberObject) =
      tangentSpace.mk p
        (pushforwardFiberObj p (cleavageOp p)
          (ArtinianLocalAlgCat.dualNumberAut derivation) fiberObject) := sorry

/-- The zero derivation acts as the identity on the tangent space. -/
theorem derivationAction_zero (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p] :
    derivationAction p 0 = id := sorry

/-- The action of a sum of derivations is the composition of their tangent-space actions. -/
theorem derivationAction_add (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsPredeformationCategory p]
    (derivation derivation' : Derivation Λ k k) :
    derivationAction p (derivation + derivation') =
      derivationAction p derivation ∘ derivationAction p derivation' := sorry

end

end CategoryTheory.Functor
