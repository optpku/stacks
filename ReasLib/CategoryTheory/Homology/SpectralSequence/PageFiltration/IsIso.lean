module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration.Naturality
public import ReasLib.CategoryTheory.Homology.PageTower.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison

/-!
# Isomorphism Transport for Spectral-Sequence Page Towers

The fixed-grading homology-page-tower construction transports isomorphisms of spectral sequences.
The bundled and component-level instances are kept together in this small leaf so downstream
arguments can use either the tower morphism or a selected page without unfolding the filtration.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory
namespace SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {κ : Type*} {c : ℤ → ComplexShape κ}

namespace HomologyTower

/-- A fixed-grading homology-page-tower map is an isomorphism when the spectral-sequence map is. -/
@[stacks 011O "isomorphism of homology-page tower maps"]
noncomputable instance map_isIso
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) [IsIso f] :
    IsIso (map f pq) := sorry

/-- Every page component of a fixed-grading tower map is an isomorphism when the spectral-sequence
map is. -/
@[stacks 011O "isomorphism on homology-page tower components"]
noncomputable instance map_app_isIso
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+) [IsIso f] :
    IsIso ((map f pq).app r) := sorry

/-- A fixed-grading homology-page-tower map is an isomorphism when the spectral-sequence map is an
isomorphism from the first page onward. -/
@[stacks 011O "tower isomorphism from a pagewise spectral-sequence comparison"]
theorem map_isIso_of_isIsoFrom
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 le_rfl) :
    IsIso (map f pq) := sorry

/-- Every page component of a fixed-grading tower map is an isomorphism when the spectral-sequence
map is an isomorphism from the first page onward. -/
@[stacks 011O "tower component from a pagewise spectral-sequence comparison"]
theorem map_app_isIso_of_isIsoFrom
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 le_rfl) :
    IsIso ((map f pq).app r) := sorry

variable {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) [IsIso f]

#synth IsIso (map f pq)
#synth IsIso ((map f pq).app 1)

end HomologyTower

namespace Cycle

/-- A fixed-grading recursive cycle map is an isomorphism when the spectral-sequence map is an
isomorphism from the first page onward. -/
@[stacks 011O "cycle-stage map from a pagewise spectral-sequence comparison"]
theorem map_isIso_of_isIsoFrom
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 le_rfl) :
    IsIso (map f pq r) := sorry

end Cycle

namespace Boundary

/-- A fixed-grading recursive boundary map is an isomorphism when the spectral-sequence map is an
isomorphism from the first page onward. -/
@[stacks 011O "boundary-stage map from a pagewise spectral-sequence comparison"]
theorem map_isIso_of_isIsoFrom
    {E E' : SpectralSequence C c 1} (f : E ⟶ E') (pq : κ) (r : ℕ+)
    (h : SpectralSequence.Hom.IsIsoFrom f 1 le_rfl) :
    IsIso (map f pq r) := sorry

end Boundary

end SpectralSequence
end CategoryTheory
