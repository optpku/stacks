module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap66.Definition_66_18_9_Square

/-!
# `f`-maps of sheaves of sets on small étale sites of algebraic spaces

An `f`-map is a family of maps of sections indexed by commutative squares of étale schemes over
`f`, compatible with restriction in both small étale sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An `f`-map `φ : 𝒢 ⟶ ℱ` of sheaves of sets on the small étale sites of algebraic spaces
`X` and `Y` is a family of maps `𝒢(V) ⟶ ℱ(U)` indexed by commutative squares of schemes étale
over `f`, compatible with restriction along morphisms in `smallEtaleSite X` and
`smallEtaleSite Y`. -/
structure FMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))) where
  /-- The component `𝒢(V) ⟶ ℱ(U)` attached to an `f`-square. -/
  app (sq : EtaleSquare f) : 𝒢.obj.obj (op sq.right) ⟶ ℱ.obj.obj (op sq.left)
  /-- Restriction in both étale sites is compatible with the components of the family. -/
  naturality {sq sq' : EtaleSquare f} (i : sq'.left ⟶ sq.left) (j : sq'.right ⟶ sq.right)
      (hij : i.left ≫ sq.map = sq'.map ≫ j.left) :
    CommSq (𝒢.obj.map j.op) (app sq) (app sq') (ℱ.obj.map i.op)

namespace FMap

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
variable {𝒢 : Sheaf (smallEtaleTopology Y) (Type (u + 1))}
variable {ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))}

/-- Two `f`-maps are equal when they have the same section components on every étale square. -/
@[ext]
theorem ext (φ ψ : FMap f 𝒢 ℱ) (h : ∀ sq : EtaleSquare f, φ.app sq = ψ.app sq) : φ = ψ :=
  sorry

/-- The component of an `f`-map on the source square `(U, V, g)`. -/
@[simp]
theorem app_ofSchemeMap (φ : FMap f 𝒢 ℱ) (U : smallEtaleSite X) (V : smallEtaleSite Y)
    (g : U.left ⟶ V.left) (w : U.hom ≫ f = ofOverMap g ≫ V.hom) :
    φ.app (EtaleSquare.ofSchemeMap U V g w) =
      φ.app { left := U, right := V, map := g, w := w } :=
  sorry

/-- Pack a source-style family `φ_{(U, V, g)} : 𝒢(V) ⟶ ℱ(U)` with its restriction compatibility
into an `f`-map. -/
def ofApp
    (component : ∀ (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
      (w : U.hom ≫ f = ofOverMap g ≫ V.hom),
      𝒢.obj.obj (op V) ⟶ ℱ.obj.obj (op U))
    (h_naturality : ∀ {U U' : smallEtaleSite X} {V V' : smallEtaleSite Y}
      (g : U.left ⟶ V.left) (g' : U'.left ⟶ V'.left)
      (w : U.hom ≫ f = ofOverMap g ≫ V.hom)
      (w' : U'.hom ≫ f = ofOverMap g' ≫ V'.hom)
      (i : U' ⟶ U) (j : V' ⟶ V) (hij : i.left ≫ g = g' ≫ j.left),
      CommSq (𝒢.obj.map j.op) (component U V g w) (component U' V' g' w')
        (ℱ.obj.map i.op)) :
    FMap f 𝒢 ℱ where
  app sq := component sq.left sq.right sq.map sq.w
  naturality {sq sq'} i j hij :=
    h_naturality sq.map sq'.map sq.w sq'.w i j hij

/-- `ofApp` recovers the given component on every source square `(U, V, g)`. -/
@[simp]
theorem ofApp_app
    (component : ∀ (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
      (w : U.hom ≫ f = ofOverMap g ≫ V.hom),
      𝒢.obj.obj (op V) ⟶ ℱ.obj.obj (op U))
    (h_naturality : ∀ {U U' : smallEtaleSite X} {V V' : smallEtaleSite Y}
      (g : U.left ⟶ V.left) (g' : U'.left ⟶ V'.left)
      (w : U.hom ≫ f = ofOverMap g ≫ V.hom)
      (w' : U'.hom ≫ f = ofOverMap g' ≫ V'.hom)
      (i : U' ⟶ U) (j : V' ⟶ V) (hij : i.left ≫ g = g' ≫ j.left),
      CommSq (𝒢.obj.map j.op) (component U V g w) (component U' V' g' w')
        (ℱ.obj.map i.op))
    (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
    (w : U.hom ≫ f = ofOverMap g ≫ V.hom) :
    (ofApp component h_naturality).app (EtaleSquare.ofSchemeMap U V g w) = component U V g w :=
  sorry

/-- The identity `f`-map of a sheaf of sets on `X_étale` is restriction along the scheme morphism
of each identity square. -/
theorem id_naturality {X : AlgebraicSpace S}
    (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))) {sq sq' : EtaleSquare (𝟙 X)}
    (i : sq'.left ⟶ sq.left) (j : sq'.right ⟶ sq.right)
    (hij : i.left ≫ sq.map = sq'.map ≫ j.left) :
    CommSq (ℱ.obj.map j.op) (ℱ.obj.map (op (EtaleSquare.homMk sq)))
      (ℱ.obj.map (op (EtaleSquare.homMk sq'))) (ℱ.obj.map i.op) :=
  sorry

/-- The identity `f`-map of a sheaf of sets on the small étale site of `X`. -/
def id {X : AlgebraicSpace S} (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    FMap (𝟙 X) ℱ ℱ where
  app sq := ℱ.obj.map (op (EtaleSquare.homMk sq))
  naturality := id_naturality ℱ

/-- The identity `f`-map acts by restriction along `EtaleSquare.homMk`. -/
@[simp]
theorem id_app {X : AlgebraicSpace S} (ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1)))
    (sq : EtaleSquare (𝟙 X)) :
    (id ℱ).app sq = ℱ.obj.map (op (EtaleSquare.homMk sq)) :=
  sorry

/-- Restriction compatibility for the identity-square family induced by a morphism of sheaves. -/
theorem ofSheafHom_naturality {X : AlgebraicSpace S}
    {𝒢 ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))} (α : 𝒢 ⟶ ℱ)
    {sq sq' : EtaleSquare (𝟙 X)} (i : sq'.left ⟶ sq.left) (j : sq'.right ⟶ sq.right)
    (hij : i.left ≫ sq.map = sq'.map ≫ j.left) :
    CommSq (𝒢.obj.map j.op)
      (α.hom.app (op sq.right) ≫ ℱ.obj.map (op (EtaleSquare.homMk sq)))
      (α.hom.app (op sq'.right) ≫ ℱ.obj.map (op (EtaleSquare.homMk sq')))
      (ℱ.obj.map i.op) :=
  sorry

/-- The identity-morphism `f`-map associated to an ordinary morphism of sheaves on
`X_étale`. -/
def ofSheafHom {X : AlgebraicSpace S} {𝒢 ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))}
    (α : 𝒢 ⟶ ℱ) : FMap (𝟙 X) 𝒢 ℱ where
  app sq := α.hom.app (op sq.right) ≫ ℱ.obj.map (op (EtaleSquare.homMk sq))
  naturality := ofSheafHom_naturality α

/-- `ofSheafHom α` sends an identity square to the sheaf-morphism component followed by
restriction. -/
@[simp]
theorem ofSheafHom_app {X : AlgebraicSpace S}
    {𝒢 ℱ : Sheaf (smallEtaleTopology X) (Type (u + 1))} (α : 𝒢 ⟶ ℱ)
    (sq : EtaleSquare (𝟙 X)) :
    (ofSheafHom α).app sq =
      α.hom.app (op sq.right) ≫ ℱ.obj.map (op (EtaleSquare.homMk sq)) :=
  sorry

/-- An `f`-map is a family of components `𝒢(V) ⟶ ℱ(U)` on source squares, compatible with
restriction along extended étale diagrams. -/
theorem spec (φ : FMap f 𝒢 ℱ) {U U' : smallEtaleSite X} {V V' : smallEtaleSite Y}
    (g : U.left ⟶ V.left) (w : U.hom ≫ f = ofOverMap g ≫ V.hom)
    (i : U' ⟶ U) (j : V' ⟶ V) (g' : U'.left ⟶ V'.left)
    (hij : i.left ≫ g = g' ≫ j.left) :
    φ.app (EtaleSquare.ofSchemeMap U V g w) =
        φ.app { left := U, right := V, map := g, w := w } ∧
      CommSq (𝒢.obj.map j.op) (φ.app (EtaleSquare.ofSchemeMap U V g w))
        (φ.app (EtaleSquare.restrict (EtaleSquare.ofSchemeMap U V g w) i j g' hij))
        (ℱ.obj.map i.op) :=
  sorry

end FMap

end AlgebraicGeometry.AlgebraicSpace
