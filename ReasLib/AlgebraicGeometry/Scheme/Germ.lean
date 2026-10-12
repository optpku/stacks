/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- A scheme germ consists of a scheme together with a distinguished point. -/
def Germ := Σ X : Scheme.{u}, X

namespace Germ

/-- The underlying scheme of a scheme germ. -/
def scheme (X : Germ) : Scheme.{u} :=
  X.1

/-- The distinguished point of a scheme germ. -/
def point (X : Germ) : X.scheme :=
  X.2

/-- Construct a germ from a scheme and one of its points. -/
def of (X : Scheme.{u}) (x : X) : Germ :=
  ⟨X, x⟩

/-- The underlying scheme of `of X x` is `X`. -/
theorem scheme_of (X : Scheme.{u}) (x : X) : (of X x).scheme = X := sorry

/-- The distinguished point of `of X x` is `x`. -/
theorem point_of (X : Scheme.{u}) (x : X) : (of X x).point = x := sorry

/-- The distinguished point, viewed as a point of an open neighborhood. -/
def pointIn (X : Germ) (U : X.scheme.Opens) (hx : X.point ∈ U) : U.toScheme :=
  ⟨X.point, hx⟩

/-- The canonical inclusion sends `X.pointIn U hx` to the distinguished point of `X`. -/
theorem pointIn_val (X : Germ) (U : X.scheme.Opens) (hx : X.point ∈ U) :
    U.ι (X.pointIn U hx) = X.point := sorry

namespace Hom

/-- A representative of a morphism of scheme germs, defined on an open neighborhood of the
source point and preserving the distinguished points. -/
structure Representative (X Y : Germ) where
  /-- The open neighborhood on which the representative is defined. -/
  neighborhood : X.scheme.Opens
  /-- The source point belongs to the representative's neighborhood. -/
  mem_neighborhood : X.point ∈ neighborhood
  /-- The scheme morphism defined on the neighborhood. -/
  hom : neighborhood.toScheme ⟶ Y.scheme
  /-- The representative sends the source point to the target point. -/
  map_point : hom (X.pointIn neighborhood mem_neighborhood) = Y.point

namespace Representative

/-- Construct a representative from a neighborhood, a scheme morphism on it, and the pointed
compatibility equation. -/
def of {X Y : Germ} (U : X.scheme.Opens) (hx : X.point ∈ U)
    (f : U.toScheme ⟶ Y.scheme) (hf : f (X.pointIn U hx) = Y.point) :
    Representative X Y :=
  ⟨U, hx, f, hf⟩

/-- The constructor `Representative.of` retains its neighborhood and morphism and preserves the
distinguished points. -/
theorem of_spec {X Y : Germ} (U : X.scheme.Opens) (hx : X.point ∈ U)
    (f : U.toScheme ⟶ Y.scheme) (hf : f (X.pointIn U hx) = Y.point) :
    (of U hx f hf).neighborhood = U ∧
      (of U hx f hf).hom = f ∧
      (of U hx f hf).hom
        (X.pointIn (of U hx f hf).neighborhood (of U hx f hf).mem_neighborhood) = Y.point := sorry

/-- Two representatives are equivalent when their restrictions agree on a common smaller open
neighborhood of the source point. -/
def Equivalent {X Y : Germ} (f g : Representative X Y) : Prop :=
  ∃ (W : X.scheme.Opens) (_ : X.point ∈ W)
    (hWf : W ≤ f.neighborhood) (hWg : W ≤ g.neighborhood),
      X.scheme.homOfLE hWf ≫ f.hom = X.scheme.homOfLE hWg ≫ g.hom

/-- The common-neighborhood formulation of equivalence of representatives. -/
theorem equivalent_iff {X Y : Germ} (f g : Representative X Y) :
    Equivalent f g ↔
      ∃ (W : X.scheme.Opens) (_ : X.point ∈ W)
        (hWf : W ≤ f.neighborhood) (hWg : W ≤ g.neighborhood),
          X.scheme.homOfLE hWf ≫ f.hom = X.scheme.homOfLE hWg ≫ g.hom := sorry

/-- Agreement on a smaller neighborhood is an equivalence relation on representatives. -/
theorem equivalent_equivalence (X Y : Germ) :
    Equivalence (@Equivalent X Y) := sorry

/-- The explicit setoid of neighborhood-defined representatives. -/
def setoid (X Y : Germ) : Setoid (Representative X Y) where
  r := Equivalent
  iseqv := equivalent_equivalence X Y

/-- The relation of `Representative.setoid` is agreement on a smaller neighborhood. -/
theorem setoid_iff {X Y : Germ} (f g : Representative X Y) :
    (setoid X Y).r f g ↔ Equivalent f g := sorry

end Representative
end Hom

/-- Morphisms of scheme germs are neighborhood-defined pointed morphisms modulo agreement on a
smaller neighborhood. -/
def Hom (X Y : Germ) := Quotient (Hom.Representative.setoid X Y)

namespace Hom

/-- Send a neighborhood representative to its germ morphism class. -/
def mk {X Y : Germ} (f : Representative X Y) : Hom X Y :=
  Quotient.mk (Representative.setoid X Y) f

/-- Two representatives determine the same germ morphism exactly when they agree on a common
smaller open neighborhood. -/
theorem mk_eq_mk_iff {X Y : Germ} (f g : Representative X Y) :
    mk f = mk g ↔ Representative.Equivalent f g := sorry

/-- Eliminate a germ morphism using a function on representatives that respects agreement on a
smaller neighborhood. -/
def lift {X Y : Germ} {α : Sort v} (F : Representative X Y → α)
    (hF : ∀ f g, Representative.Equivalent f g → F f = F g) : Hom X Y → α :=
  Quotient.lift F hF

/-- Evaluating `Hom.lift` on a represented germ morphism evaluates the representative function. -/
theorem lift_mk {X Y : Germ} {α : Sort v} (F : Representative X Y → α)
    (hF : ∀ f g, Representative.Equivalent f g → F f = F g)
    (f : Representative X Y) : lift F hF (mk f) = F f := sorry

/-- Every point belongs to the top open neighborhood of its scheme. -/
theorem mem_top (X : Germ) : X.point ∈ (⊤ : X.scheme.Opens) := sorry

/-- Restricting a global pointed morphism to the top open still preserves the distinguished
point. -/
theorem ofGlobal_mapPoint {X Y : Germ} (f : X.scheme ⟶ Y.scheme)
    (hf : f X.point = Y.point) :
    ((⊤ : X.scheme.Opens).ι ≫ f) (X.pointIn ⊤ (mem_top X)) = Y.point := sorry

/-- Regard a global pointed scheme morphism as a morphism of germs. -/
def ofGlobal {X Y : Germ} (f : X.scheme ⟶ Y.scheme) (hf : f X.point = Y.point) : Hom X Y :=
  mk (Representative.of ⊤ (mem_top X) ((⊤ : X.scheme.Opens).ι ≫ f)
    (ofGlobal_mapPoint f hf))

/-- A global pointed morphism is represented on the top open neighborhood. -/
theorem ofGlobal_mk {X Y : Germ} (f : X.scheme ⟶ Y.scheme) (hf : f X.point = Y.point) :
    ofGlobal f hf =
      mk (Representative.of ⊤ (mem_top X) ((⊤ : X.scheme.Opens).ι ≫ f)
        (ofGlobal_mapPoint f hf)) := sorry

namespace Representative

/-- The open neighborhood on which two representatives may be composed. -/
def compNeighborhood {X Y Z : Germ} (f : Representative X Y) (g : Representative Y Z) :
    X.scheme.Opens :=
  f.neighborhood.ι ''ᵁ (f.hom ⁻¹ᵁ g.neighborhood)

/-- The source point belongs to the neighborhood used for representative composition. -/
theorem mem_compNeighborhood {X Y Z : Germ} (f : Representative X Y)
    (g : Representative Y Z) : X.point ∈ compNeighborhood f g := sorry

/-- The scheme morphism obtained by restricting the first representative to the preimage of the
second neighborhood and then composing with the second representative. -/
def compMap {X Y Z : Germ} (f : Representative X Y) (g : Representative Y Z) :
    (compNeighborhood f g).toScheme ⟶ Z.scheme :=
  (f.neighborhood.ι.isoImage (f.hom ⁻¹ᵁ g.neighborhood)).inv ≫
    (f.hom ∣_ g.neighborhood) ≫ g.hom

/-- The representative-level composite map preserves the distinguished points. -/
theorem compMap_point {X Y Z : Germ} (f : Representative X Y) (g : Representative Y Z) :
    compMap f g (X.pointIn (compNeighborhood f g) (mem_compNeighborhood f g)) = Z.point := sorry

/-- Compose two neighborhood representatives on the canonical open neighborhood where their
scheme morphisms can be composed. -/
def comp {X Y Z : Germ} (f : Representative X Y) (g : Representative Y Z) :
    Representative X Z :=
  Representative.of (compNeighborhood f g) (mem_compNeighborhood f g)
    (compMap f g) (compMap_point f g)

/-- The neighborhood of a representative composite is the image of the relevant preimage open. -/
theorem comp_neighborhood {X Y Z : Germ} (f : Representative X Y) (g : Representative Y Z) :
    (comp f g).neighborhood = f.neighborhood.ι ''ᵁ (f.hom ⁻¹ᵁ g.neighborhood) := sorry

/-- The morphism of a representative composite is the composite of the canonical restriction
maps. -/
theorem comp_hom {X Y Z : Germ} (f : Representative X Y) (g : Representative Y Z) :
    (comp f g).hom =
      (f.neighborhood.ι.isoImage (f.hom ⁻¹ᵁ g.neighborhood)).inv ≫
        (f.hom ∣_ g.neighborhood) ≫ g.hom := sorry

/-- Representative composition respects agreement on smaller neighborhoods in both variables. -/
theorem comp_respects {X Y Z : Germ} {f f' : Representative X Y}
    (hf : (setoid X Y).r f f') {g g' : Representative Y Z}
    (hg : (setoid Y Z).r g g') : (setoid X Z).r (comp f g) (comp f' g') := sorry

end Representative

/-- Composition of germ morphisms, induced by composition of neighborhood representatives. -/
def comp {X Y Z : Germ} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  Quotient.map₂ Representative.comp (@Representative.comp_respects X Y Z) f g

/-- Composition of represented germ morphisms is represented by the composite of their
representatives. -/
theorem comp_mk {X Y Z : Germ} (f : Representative X Y) (g : Representative Y Z) :
    comp (mk f) (mk g) = mk (Representative.comp f g) := sorry

/-- The identity morphism of a germ preserves its distinguished point. -/
theorem id_mapPoint (X : Germ) : (𝟙 X.scheme) X.point = X.point := sorry

/-- The identity morphism of a scheme germ. -/
def id (X : Germ) : Hom X X :=
  ofGlobal (𝟙 X.scheme) (id_mapPoint X)

/-- The identity germ morphism is represented by the canonical inclusion of the top open. -/
theorem id_mk (X : Germ) :
    id X = mk (Representative.of ⊤ (mem_top X)
      ((⊤ : X.scheme.Opens).ι ≫ 𝟙 X.scheme)
      (ofGlobal_mapPoint (𝟙 X.scheme) (id_mapPoint X))) := sorry

/-- Left identity law for composition of germ morphisms. -/
theorem id_comp {X Y : Germ} (f : Hom X Y) : comp (id X) f = f := sorry

/-- Right identity law for composition of germ morphisms. -/
theorem comp_id {X Y : Germ} (f : Hom X Y) : comp f (id Y) = f := sorry

/-- Associativity of composition of germ morphisms. -/
theorem assoc {W X Y Z : Germ} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

end Hom
end Germ
end AlgebraicGeometry.Scheme
