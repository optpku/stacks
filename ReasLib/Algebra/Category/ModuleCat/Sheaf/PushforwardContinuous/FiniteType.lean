module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.FiniteType
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType.Zero
public import ReasLib.Topology.Sheaves.Abelian.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite type under continuous pushforward

This file owns the topological part of finite generation under direct image. Reflection uses
only that the source topology is induced from the target. Preservation additionally uses a
closed image and local surjectivity of the map of ring sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.PushforwardContinuous

variable {X Y : TopCat.{u}}
variable {S : Y.Sheaf RingCat.{v}} {R : X.Sheaf RingCat.{v}}

namespace Inducing

/-- If the source topology is induced from the target, finite type of a module direct image
reflects to the original module sheaf. No surjectivity assumption on the ring map is needed. -/
@[stacks 01C4 "inducing reflection"]
theorem of_pushforward_isFiniteType
    (f : X ⟶ Y) (hf : Topology.IsInducing f)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{v} f).obj R)
    (M : SheafOfModules.{v} R)
    (hM : ((SheafOfModules.pushforward φ).obj M).IsFiniteType) :
    M.IsFiniteType := sorry

end Inducing

namespace ClosedEmbedding

/-- Direct image along a closed embedding and a locally surjective map of ring sheaves
preserves finite type. -/
@[stacks 01C4 "closed embedding preservation"]
theorem isFiniteType
    (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{v} f).obj R)
    [Sheaf.IsLocallySurjective φ]
    (M : SheafOfModules.{v} R) [M.IsFiniteType] :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := sorry

/-- For a closed embedding with a locally surjective map of ring sheaves, direct image
preserves and reflects finite type. -/
@[stacks 01C4 "topological core"]
theorem isFiniteType_iff
    (f : X ⟶ Y) (hf : Topology.IsClosedEmbedding f)
    (φ : S ⟶ (TopCat.Sheaf.pushforward RingCat.{v} f).obj R)
    [Sheaf.IsLocallySurjective φ]
    (M : SheafOfModules.{v} R) :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType ↔ M.IsFiniteType := sorry

end ClosedEmbedding

end SheafOfModules.PushforwardContinuous
