module

public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap67.Lemma_67_8_10_Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.8.10 (1): if `X` is quasi-compact and `Y` is quasi-separated, then `f` is
quasi-compact. -/
@[stacks 073B] #check
  (QuasiCompact.of_isQuasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y],
      QuasiCompact f)

/- Lemma 67.8.10 (2): if `X` is quasi-compact and quasi-separated and `Y` is
quasi-separated, then `f` is quasi-compact and quasi-separated. -/
@[stacks 073B] #check
  (QuasiCompact.of_isQuasiCompact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y],
      QuasiCompact f)

@[stacks 073B] #check
  (QuasiSeparated.of_isAbsolutelyQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsAbsolutelyQuasiSeparated X],
      QuasiSeparated f)

/- Lemma 67.8.10 (3): a fibre product of quasi-compact and quasi-separated algebraic
spaces is quasi-compact and quasi-separated. -/
@[stacks 073B] #check
  (IsQuasiCompact.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S} {f : X ⟶ Y} {g : Z ⟶ Y}
      {pZ : P ⟶ Z} {pX : P ⟶ X}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] [IsQuasiCompact Z],
      IsPullback pZ pX g f → IsQuasiCompact P)

@[stacks 073B] #check
  (IsAbsolutelyQuasiSeparated.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S} {f : X ⟶ Y} {g : Z ⟶ Y}
      {pZ : P ⟶ Z} {pX : P ⟶ X}
      [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z],
      IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P)

@[stacks 073B] #check
  (IsQuasiCompact.instPullback :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated Y] [IsQuasiCompact Z]
      [HasPullback f g],
      IsQuasiCompact (pullback f g))

@[stacks 073B] #check
  (IsAbsolutelyQuasiSeparated.instPullback :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsAbsolutelyQuasiSeparated X] [IsAbsolutelyQuasiSeparated Z]
      [HasPullback f g],
      IsAbsolutelyQuasiSeparated (pullback f g))

end AlgebraicGeometry.AlgebraicSpace
