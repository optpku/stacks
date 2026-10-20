module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Along

/-!
# Compatibility checks for filtration-indexed formal objects
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

#check (FormalObject.Along :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) (R : CompleteLocalAlgCat Λ k)
    (I : CompleteLocalAlgCat.AdicIdealFiltration R), Type v)

#check (FormalObject.Along.toFiber :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (R : CompleteLocalAlgCat Λ k)
    (I : CompleteLocalAlgCat.AdicIdealFiltration R),
    -- Local instance justification (defeq pin): the checked functor type must use the explicit category of filtration-indexed systems.
    letI := FormalObject.Along.category (p := p) (R := R) (I := I)
    FormalObject.Along p R I ⥤ Functor.Fiber (Functor.completion p) R)
