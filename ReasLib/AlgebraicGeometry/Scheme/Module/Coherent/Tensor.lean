module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# Tensor closure of coherent scheme modules

Tensor products of coherent modules on a locally Noetherian scheme are coherent.
The corresponding internal-Hom closure theorem is reexported for compatibility.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {X : Scheme.{u}}
variable {F G : X.Modules}
variable [IsLocallyNoetherian X]

/-- The tensor unit of scheme modules is coherent on a locally Noetherian scheme. -/
theorem tensorUnit_isCoherent_of_isLocallyNoetherian :
    (𝟙_ X.Modules).IsCoherent := sorry

/-- The tensor unit of scheme modules is canonically coherent on a locally Noetherian scheme. -/
instance instIsCoherentTensorUnit : (𝟙_ X.Modules).IsCoherent :=
  tensorUnit_isCoherent_of_isLocallyNoetherian

/-- The tensor product of coherent modules on a locally Noetherian scheme is coherent. -/
@[stacks 01Y2, instance]
theorem isCoherent_tensor
    [F.IsCoherent] [G.IsCoherent] :
    (F ⊗ G).IsCoherent := sorry

end

/-- On a scheme proper over a field, tensoring a coherent module with a finite locally free
module of constant rank produces a coherent module. -/
theorem isCoherent_tensor_of_isProper_over_field
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (F : X.Modules) [F.IsCoherent]
    (n : ℕ) (G : X.Modules) [IsFiniteLocallyFreeOfRank n G] :
    (F ⊗ G : X.Modules).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
