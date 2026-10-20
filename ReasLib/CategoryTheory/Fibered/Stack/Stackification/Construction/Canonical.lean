module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.HomConditions
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification

/-!
# Canonical stackification from the original fibred projection

The original fibredness supplies the internal cleavage. The target, comparison,
local Hom preimages and local object models are the explicit local descent
construction; no model or presentation is required from the caller.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) [p.IsFibered]

/-- The canonical completed stack uses the original fibred projection's native cleavage. -/
def canonicalTarget : StackOver.{u, v, max u v uX vX, max u v vX} J :=
  targetStack J p (Cleavage.ofIsFibered p)

/-- The canonical comparison retains the original object and local descent maps. -/
def canonicalComparison : CartesianBasedFunctor p (canonicalTarget J p).p :=
  comparison J p (Cleavage.ofIsFibered p)

/-- Both local conditions and the actual target stack assemble the canonical predicate. -/
theorem canonicalIsStackification :
    CartesianBasedFunctor.IsStackification J (canonicalComparison J p) where
  isLocalEquivalence := comparisonIsLocalEquivalence J p (Cleavage.ofIsFibered p)
  isStack := targetIsStack J p (Cleavage.ofIsFibered p)

variable [hG : Functor.IsFibered.InGroupoids p]

/-- Original groupoid fibres give the canonical target its actual inverse operations. -/
def canonicalGroupoidTarget :
    StackOver.Groupoids.{u, v, max u v uX vX, max u v vX} J :=
  targetGroupoids J p (Cleavage.ofIsFibered p) hG

/-- The canonical groupoid comparison uses the same actual object and arrow maps. -/
def canonicalGroupoidComparison :
    CartesianBasedFunctor p (canonicalGroupoidTarget J p).p :=
  groupoidComparison J p (Cleavage.ofIsFibered p) hG

/-- The canonical groupoid comparison carries the two explicit local conditions. -/
theorem canonicalGroupoidIsStackification :
    CartesianBasedFunctor.IsStackification J (canonicalGroupoidComparison J p) where
  isLocalEquivalence := comparisonIsLocalEquivalence J p (Cleavage.ofIsFibered p)
  isStack := targetIsStack J p (Cleavage.ofIsFibered p)

end CategoryTheory.Functor.StackificationConstruction
