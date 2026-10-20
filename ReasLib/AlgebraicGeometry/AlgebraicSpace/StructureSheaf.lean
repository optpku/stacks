module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite
public import Mathlib.Algebra.Category.Ring.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale

/-- The structure presheaf on étale charts assigns the ring of global sections of each
underlying scheme. -/
def structurePresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (site X)ᵒᵖ ⥤ RingCat.{u} :=
  (toScheme X).op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat RingCat

/-- The global-sections structure presheaf satisfies descent for the small étale topology. -/
theorem structurePresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (topology X) (structurePresheaf X) := sorry

/-- The structure sheaf on the small étale site has the global-sections presheaf as its
underlying presheaf of rings. -/
def structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (topology X) RingCat.{u} :=
  ⟨structurePresheaf X, structurePresheaf_isSheaf X⟩

end AlgebraicGeometry.AlgebraicSpace.SmallEtale
