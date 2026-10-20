module

public import ReasLib.AlgebraicGeometry.FormalDeformation.EssentialSurjection.Quotient
import StacksCheckRecall

/-!
# Essential surjections modulo squares

A morphism in `C_Λ` is an essential surjection if and only if the induced maps
on quotients by `maximalIdeal ^ 2` and by `relativeDenom` are essential
surjections.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.3.10 (1): essential surjectivity is detected modulo maximal-ideal squares. -/
@[stacks 06S5] #check (ArtinianLocalAlgCat.isEssentialSurjection_iff_modSquare :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    ArtinianLocalAlgCat.IsEssentialSurjection f ↔
      ArtinianLocalAlgCat.IsEssentialSurjection (ArtinianLocalAlgCat.modSquareMap f))

/- Lemma 90.3.10 (2): essential surjectivity is detected on relative infinitesimal quotients. -/
@[stacks 06S5] #check (ArtinianLocalAlgCat.isEssentialSurjection_iff_modRelative :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    ArtinianLocalAlgCat.IsEssentialSurjection f ↔
      ArtinianLocalAlgCat.IsEssentialSurjection (ArtinianLocalAlgCat.modRelativeMap f))

#check (ArtinianLocalAlgCat.isEssentialSurjection_modSquare_iff_modRelative :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    ArtinianLocalAlgCat.IsEssentialSurjection (ArtinianLocalAlgCat.modSquareMap f) ↔
      ArtinianLocalAlgCat.IsEssentialSurjection (ArtinianLocalAlgCat.modRelativeMap f))
