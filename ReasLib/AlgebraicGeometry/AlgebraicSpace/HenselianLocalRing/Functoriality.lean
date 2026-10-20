module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Functoriality through actual pointed elementary neighbourhoods

For f : X → Y and f(x)=y, a section over an elementary neighbourhood V of y
pulls back to a section over an actual elementary neighbourhood W of x mapping
to V over f. Its image in the neighbourhood colimit is independent of W.
Conditional reconstruction chooses only an actual such value. The range and
uniqueness laws express elementary étale pullback/refinement, not étaleness of
a residue-field morphism. This is the colimit form of Stacks Remark 68.11.11.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.HenselianFunctoriality
variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]

/-- An actual pointed map of elementary neighbourhoods over the given space morphism. -/
structure PointedNeighborhoodMap (f : X ⟶ Y) {x : Points X} {y : Points Y}
    (W : EtaleNeighborhood.Elementary X x) (V : EtaleNeighborhood.Elementary Y y) where
  /-- The underlying scheme morphism, with its structural map to S preserved. -/
  overHom : W.obj.toOver ⟶ V.obj.toOver
  /-- The map lies over f. -/
  over_fac : ofOverMap overHom ≫ V.obj.hom = W.obj.hom ≫ f
  /-- The selected source point maps to the selected target point. -/
  map_point : overHom.left W.obj.point = V.obj.point

/-- Pull an actual representative section to W and then into its henselian colimit. -/
def representativeHom (f : X ⟶ Y) {x : Points X} {y : Points Y}
    {W : EtaleNeighborhood.Elementary X x} {V : EtaleNeighborhood.Elementary Y y}
    (m : PointedNeighborhoodMap f W V) :
    (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V)) ⟶
      henselianLocalRingCat X x :=
  (CommRingCat.universeLift.{u, u + 1}).map (Scheme.Γ.map m.overHom.left.op) ≫
    colimit.ι (EtaleNeighborhood.Elementary.sections X x) (ULiftHom.objUp (op W))

/-- A colimit value is represented by an actual pointed elementary neighbourhood over V. -/
def IsValue (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (V : EtaleNeighborhood.Elementary Y y)
    (a : (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V)))
    (b : henselianLocalRing X x) : Prop :=
  ∃ (W : EtaleNeighborhood.Elementary X x) (m : PointedNeighborhoodMap f W V),
    (representativeHom f m).hom a = b

/-- Select only an actual represented value; zero totalizes inputs without a representative. -/
def sectionValue (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (V : EtaleNeighborhood.Elementary Y y)
    (a : (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V))) :
    henselianLocalRing X x := by
  classical
  exact if h : ∃ b, IsValue f x y V a b then Classical.choose h else 0

/-- If f(x)=y, elementary refinement of the actual pullback supplies a represented value. -/
theorem value_inRange (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (V : EtaleNeighborhood.Elementary Y y)
    (a : (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V))) :
    ∃ b, IsValue f x y V a b := sorry

/-- Two pointed refinements agree after a common refinement and restriction to the étale diagonal. -/
theorem value_unique (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (V : EtaleNeighborhood.Elementary Y y)
    (a : (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V)))
    {b c : henselianLocalRing X x}
    (hb : IsValue f x y V a b) (hc : IsValue f x y V a c) : b = c := sorry

/-- On the pointed domain the selected section has an actual representative. -/
theorem sectionValue_spec (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (V : EtaleNeighborhood.Elementary Y y)
    (a : (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V))) :
    IsValue f x y V a (sectionValue f x y V a) := by
  classical
  unfold sectionValue
  split_ifs with h
  · exact Classical.choose_spec h
  · exact False.elim (h (value_inRange f x y hxy V a))

/-- An explicitly supplied pointed representative computes the selected colimit value. -/
theorem sectionValue_of_representative (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (V : EtaleNeighborhood.Elementary Y y)
    (W : EtaleNeighborhood.Elementary X x) (m : PointedNeighborhoodMap f W V)
    (a : (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V))) :
    sectionValue f x y V a = (representativeHom f m).hom a :=
  value_unique f x y hxy V a (sectionValue_spec f x y hxy V a) ⟨W, m, rfl⟩

/-- The selected section function is a ring homomorphism on the domain f(x)=y. -/
def sectionRingHom (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (V : EtaleNeighborhood.Elementary Y y) :
    (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V)) →+*
      henselianLocalRing X x where
  toFun := sectionValue f x y V
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- A component of the target elementary-neighbourhood diagram's cocone. -/
def component (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (V : EtaleNeighborhood.Elementary Y y) :
    (EtaleNeighborhood.Elementary.sections Y y).obj (ULiftHom.objUp (op V)) ⟶
      henselianLocalRingCat X x :=
  CommRingCat.ofHom (sectionRingHom f x y hxy V)

/-- The local ring map induced by the actual pointed-neighbourhood cocone. -/
def map (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) :
    henselianLocalRing Y y →+* henselianLocalRing X x :=
  (colimit.desc (EtaleNeighborhood.Elementary.sections Y y)
    { pt := henselianLocalRingCat X x
      ι := { app := fun j ↦ component f x y hxy (ULiftHom.objDown j).unop
             naturality := sorry } }).hom

/-- The induced homomorphism sends a section to its restriction on any actual pointed
elementary refinement over the target neighbourhood. -/
theorem map_ι (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) (V : EtaleNeighborhood.Elementary Y y)
    (W : EtaleNeighborhood.Elementary X x) (m : PointedNeighborhoodMap f W V) :
    (map f x y hxy).comp (henselianLocalRing.ι Y y V) =
      (henselianLocalRing.ι X x W).comp (Scheme.Γ.map m.overHom.left.op).hom := sorry

/-- The homomorphism induced by the identity of a pointed algebraic space is the identity. -/
@[simp]
theorem map_id (x : Points X) :
    map (𝟙 X) x x (Points.map_id x) = RingHom.id (henselianLocalRing X x) := sorry

/-- Pullback on henselian local rings reverses composition of pointed space morphisms. -/
theorem map_comp {Z : AlgebraicSpace S} [IsDecent Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Points X) (y : Points Y) (z : Points Z)
    (hxy : Points.map f x = y) (hyz : Points.map g y = z) :
    map (f ≫ g) x z ((Points.map_comp f g x).trans ((congrArg (Points.map g) hxy).trans hyz)) =
      (map f x y hxy).comp (map g y z hyz) := sorry

/-- The homomorphism on henselian local rings induced by a pointed space morphism is local. -/
instance map_isLocalHom (f : X ⟶ Y) (x : Points X) (y : Points Y)
    (hxy : Points.map f x = y) : IsLocalHom (map f x y hxy) := sorry

end AlgebraicGeometry.AlgebraicSpace.HenselianFunctoriality
