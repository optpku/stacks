module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Functorial
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

/-!
# Compatible local deformations of maps of algebraic spaces

Given first-order thickenings `X ⊂ X'` and `Y ⊂ Y'` over `B`, a map
`a : X ⟶ Y`, and an `𝒪_X`-linear comparison of conormal sheaves, each object
`U'` of `X'_spaces,étale` is assigned the set of maps `U'.left ⟶ Y'` over `B`
that restrict to `a` on `X ×_{X'} U'` and induce the given conormal comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}

/-- The fibre product `U = X ×_{X'} U'` for an object of the spaces-étale site of `X'`. -/
abbrev closedSpace (iX : X ⟶ X') (U' : spacesEtaleSite X') : AlgebraicSpace S :=
  ((spacesEtalePullback iX).obj U').left

/-- The projection `U ⟶ U'` from the fibre product `U = X ×_{X'} U'`. -/
abbrev closedι (iX : X ⟶ X') (U' : spacesEtaleSite X') : closedSpace iX U' ⟶ U'.left :=
  pullback.fst U'.hom iX

/-- The projection `U ⟶ X` of the fibre product `X ×_{X'} U'`. -/
abbrev toSource (iX : X ⟶ X') (U' : spacesEtaleSite X') : closedSpace iX U' ⟶ X :=
  pullback.snd U'.hom iX

/-- Base change of a closed immersion along an étale map of algebraic spaces remains a
closed immersion. -/
instance closedι_isClosedImmersion (iX : X ⟶ X') (U' : spacesEtaleSite X')
    [IsClosedImmersion iX] : IsClosedImmersion (closedι iX U') := sorry

/-- The cartesian commutative square of the fibre product `U = X ×_{X'} U'`. -/
def thickeningPullbackSq (iX : X ⟶ X') (U' : spacesEtaleSite X') :
    CommSq (toSource iX U') (closedι iX U') iX U'.hom :=
  (IsPullback.of_hasPullback U'.hom iX).flip.toCommSq

/-- The conormal map induced by a commutative square of a candidate local lift. -/
noncomputable def inducedConormalMap (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsClosedImmersion iX] [IsImmersion iY] (U' : spacesEtaleSite X')
    (a' : U'.left ⟶ Y')
    (sq : CommSq (toSource iX U' ≫ a) (closedι iX U') iY a') :
    (Modules.pullback (toSource iX U')).obj
        ((Modules.pullback a).obj (conormalSheaf iY)) ⟶
      conormalSheaf (closedι iX U') :=
  (Modules.pullbackCompIso (toSource iX U') a).hom.app (conormalSheaf iY) ≫ Conormal.map sq

/-- The explicit composite defining `inducedConormalMap`. -/
theorem inducedConormalMap_def (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsClosedImmersion iX] [IsImmersion iY] (U' : spacesEtaleSite X')
    (a' : U'.left ⟶ Y')
    (sq : CommSq (toSource iX U' ≫ a) (closedι iX U') iY a') :
    inducedConormalMap iX iY a U' a' sq =
      (Modules.pullbackCompIso (toSource iX U') a).hom.app (conormalSheaf iY) ≫
        Conormal.map sq := sorry

/-- The restriction of a fixed conormal comparison to `U`, transported along the
cartesian base-change square. -/
noncomputable def restrictedConormalMap (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsClosedImmersion iX] [IsImmersion iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') :
    (Modules.pullback (toSource iX U')).obj
        ((Modules.pullback a).obj (conormalSheaf iY)) ⟶
      conormalSheaf (closedι iX U') :=
  (Modules.pullback (toSource iX U')).map A ≫ Conormal.map (thickeningPullbackSq iX U')

/-- The explicit composite defining `restrictedConormalMap`. -/
theorem restrictedConormalMap_def (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsClosedImmersion iX] [IsImmersion iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') :
    restrictedConormalMap iX iY a A U' =
      (Modules.pullback (toSource iX U')).map A ≫
        Conormal.map (thickeningPullbackSq iX U') := sorry

/-- A local lift is compatible with the base, the given map on `U`, and the
prescribed conormal comparison. -/
def IsCompatible (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y') : Prop :=
  a' ≫ sY' = U'.hom ≫ sX' ∧
    ∃ sq : CommSq (toSource iX U' ≫ a) (closedι iX U') iY a',
      inducedConormalMap iX iY a U' a' sq = restrictedConormalMap iX iY a A U'

/-- A local lift is compatible exactly when it is over `B`, restricts to `a` on `U`,
and induces the restriction of the prescribed conormal map `A`. -/
theorem isCompatible_iff (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y') :
    IsCompatible sX' sY' iX iY a A U' a' ↔
      a' ≫ sY' = U'.hom ≫ sX' ∧
        ∃ sq : CommSq (toSource iX U' ≫ a) (closedι iX U') iY a',
          inducedConormalMap iX iY a U' a' sq =
            restrictedConormalMap iX iY a A U' := sorry

/-- The set of compatible local deformations of `a` on an object of the
spaces-étale site of `X'`. -/
def sections (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') : Set (U'.left ⟶ Y') :=
  {a' | IsCompatible sX' sY' iX iY a A U' a'}

/-- Membership in `sections` is the local compatibility predicate. -/
theorem mem_sections_iff (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y') :
    a' ∈ sections sX' sY' iX iY a A U' ↔ IsCompatible sX' sY' iX iY a A U' a' :=
  sorry

/-- Restrict a candidate local deformation along a morphism of spaces-étale objects. -/
def restrictHom {U' V' : spacesEtaleSite X'} (f : V' ⟶ U') (a' : U'.left ⟶ Y') :
    V'.left ⟶ Y' :=
  f.left ≫ a'

/-- Restriction of a candidate along the identity is unchanged. -/
theorem restrictHom_id (U' : spacesEtaleSite X') (a' : U'.left ⟶ Y') :
    restrictHom (𝟙 U') a' = a' := sorry

/-- Successive restrictions agree with restriction along the composite. -/
theorem restrictHom_comp {U' V' W' : spacesEtaleSite X'} (f : W' ⟶ V') (g : V' ⟶ U')
    (a' : U'.left ⟶ Y') :
    restrictHom f (restrictHom g a') = restrictHom (f ≫ g) a' := sorry

/-- Restricting a compatible local deformation yields a compatible local deformation. -/
theorem mem_sections_restrictHom (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    {U' V' : spacesEtaleSite X'} (f : V' ⟶ U') (a' : U'.left ⟶ Y')
    (ha' : a' ∈ sections sX' sY' iX iY a A U') :
    restrictHom f a' ∈ sections sX' sY' iX iY a A V' := sorry


end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
