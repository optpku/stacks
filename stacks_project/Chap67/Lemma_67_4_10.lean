module

public import stacks_project.Chap67.Lemma_67_4_10_Postcomp
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.4.10 (1): if `g ∘ f` is separated then so is `f`. -/
@[stacks 03KR] #check
  (Separated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [Separated (f ≫ g)], Separated f)

/- Lemma 67.4.10 (2): if `g ∘ f` is locally separated then so is `f`. -/
@[stacks 03KR] #check
  (LocallySeparated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallySeparated (f ≫ g)], LocallySeparated f)

/- Lemma 67.4.10 (3): if `g ∘ f` is quasi-separated then so is `f`. -/
@[stacks 03KR] #check
  (QuasiSeparated.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [QuasiSeparated (f ≫ g)], QuasiSeparated f)
