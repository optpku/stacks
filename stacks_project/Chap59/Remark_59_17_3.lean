module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Terminal
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/- Remark 59.17.3: when `C` has a final object `S`, quasi-coherence is
equivalent to the existence of a covering family of `S` whose restrictions
admit global presentations. -/
@[stacks 03OI] #check
  (SheafOfModules.IsQuasicoherent.iff_existsPresentation_of_isTerminal :
    ∀ (M : SheafOfModules.{w} R) (S : C) (hS : IsTerminal S),
      M.IsQuasicoherent ↔
        ∃ (I : Type u) (X : I → C),
          Sieve.ofObjects X S ∈ J S ∧
            ∀ i : I, Nonempty (M.over (X i)).Presentation)
