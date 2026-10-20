module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger

/-!
# Localization of Schlessinger conditions

Schlessinger conditions are preserved by slicing at an object in the residue
fibre and applying the forgetful functor from the resulting over category.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Slicing a functor satisfying Schlessinger's condition (S1) at a residue-fibre
object preserves condition (S1). -/
instance instHasSchlessingerS1_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    HasSchlessingerS1 (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

/-- Slicing a functor satisfying Schlessinger's condition (S2) at a residue-fibre
object preserves condition (S2). -/
instance instHasSchlessingerS2_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    HasSchlessingerS2 (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

end CategoryTheory.Functor
