module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Definition_90_19_2_DualNumber
public import stacks_project.Chap90.Definition_90_23_1
public import stacks_project.Chap90.Definition_90_25_1_Quotient

/-!
# Deformation categories as quotients of smooth groupoids in functors

If `(U, R, s, t, c)` is a smooth groupoid in functors on `ArtinianLocalAlgCat Λ k` and
`U`, `R` are deformation functors, then the quotient `[U/R]` is a deformation category,
its tangent space is the coequalizer of `ds` and `dt` at `dualNumber Λ k`, and its
infinitesimal automorphisms are the kernel of `ds ⊕ dt` at the origin.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor Fiber

noncomputable section

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Lemma 90.24.2 (1): if `(U, R, s, t, c)` is a smooth groupoid in functors on
`ArtinianLocalAlgCat Λ k` and `U`, `R` are deformation functors, then the quotient
`[U/R]` is a deformation category. -/
@[stacks 06KU]
instance instIsDeformationCategory_quotient
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)] :
    Functor.IsDeformationCategory G.quotient.p := sorry

/-- The quotient `[U/R]` of a smooth groupoid in functors with deformation-functor object
and arrow functors is a predeformation category satisfying (RS). -/
theorem isDeformationCategory_quotient_spec
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)] :
    Functor.IsPredeformationCategory G.quotient.p ∧
      Functor.HasRimSchlessinger G.quotient.p := sorry

/-- The Grothendieck object `(dualNumber Λ k, x)` of `[U/R]` lies over `dualNumber Λ k`. -/
theorem quotientMkObj_over
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    (x : G.U.obj (dualNumber Λ k)) :
    G.quotient.p.obj (Functor.ofGroupoidValued.mkObj G.toFunctor (dualNumber Λ k) x) =
      dualNumber Λ k := sorry

/-- The dual-number fibre object of `[U/R]` associated to a point of `U(k[ε])`. -/
def tangentSpaceQuotientFiber
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x : G.U.obj (dualNumber Λ k)) :
    G.quotient.p.Fiber (dualNumber Λ k) :=
  Functor.Fiber.mk (quotientMkObj_over G x)

/-- The dual-number fibre object of `[U/R]` associated to `x` lies over `dualNumber Λ k`. -/
theorem tangentSpaceQuotientFiber_over
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x : G.U.obj (dualNumber Λ k)) :
    G.quotient.p.obj (fiberInclusion.obj (tangentSpaceQuotientFiber G x)) =
      dualNumber Λ k := sorry

/-- The tangent space of the quotient `[U/R]`, as isomorphism classes in the dual-number fibre. -/
abbrev tangentSpaceQuotient
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)] :=
  isomorphismClasses.obj (Cat.of (G.quotient.p.Fiber (dualNumber Λ k)))

/-- `tangentSpaceQuotient` is the type of isomorphism classes of the dual-number fibre of
`[U/R]`. -/
theorem tangentSpaceQuotient_def
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)] :
    tangentSpaceQuotient G =
      isomorphismClasses.obj (Cat.of (G.quotient.p.Fiber (dualNumber Λ k))) := sorry

/-- The comparison map `TU → T[U/R]` sending a dual-number object of `U` to its class in
the tangent space of the quotient. -/
def tangentSpaceQuotientMk
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x : G.U.obj (dualNumber Λ k)) :
    tangentSpaceQuotient G :=
  Quotient.mk (isIsomorphicSetoid _) (tangentSpaceQuotientFiber G x)

/-- `tangentSpaceQuotientMk` is the isomorphism class of the dual-number fibre object
associated to `x`. -/
theorem tangentSpaceQuotientMk_apply
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x : G.U.obj (dualNumber Λ k)) :
    tangentSpaceQuotientMk G x =
      Quotient.mk (isIsomorphicSetoid _) (tangentSpaceQuotientFiber G x) := sorry

/-- The comparison `TU → T[U/R]` is surjective: every tangent vector of `[U/R]` arises from
an object of `U(k[ε])`. -/
theorem tangentSpaceQuotientMk_surjective
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)] :
    Function.Surjective (tangentSpaceQuotientMk G) := sorry

/-- Lemma 90.24.2 (2): the tangent space of `[U/R]` is `T[U/R] = Coker(ds - dt : TR → TU)`.
Two objects of `U(k[ε])` determine the same class in `T[U/R]` if and only if they are the
source and target of an arrow of `R` at `dualNumber Λ k`, so `T[U/R]` is the coequalizer of
`G.s.app (dualNumber Λ k)` and `G.t.app (dualNumber Λ k)`. -/
@[stacks 06KU]
theorem tangentSpace_quotient
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x y : G.U.obj (dualNumber Λ k)) :
    tangentSpaceQuotientMk G x = tangentSpaceQuotientMk G y ↔
      Nonempty (G.PointHom (dualNumber Λ k) x y) := sorry

/-- The origin of `U` in `U(k[ε])`, obtained by pushing a residue-fibre object along
`residueToDualNumber`. -/
def origin (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    (x0 : G.U.obj (residue Λ k)) : G.U.obj (dualNumber Λ k) :=
  G.U.map (residueToDualNumber Λ k) x0

/-- The origin is the image of the chosen residue object under `U.map residueToDualNumber`. -/
theorem origin_apply (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    (x0 : G.U.obj (residue Λ k)) :
    origin G x0 = G.U.map (residueToDualNumber Λ k) x0 := sorry

/-- Infinitesimal automorphisms of `[U/R]` as arrows of `R` based at the origin of `U`.
This is the kernel of `ds ⊕ dt : TR → TU ⊕ TU`. -/
abbrev infAutQuotient (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x0 : G.U.obj (residue Λ k)) :=
  G.PointHom (dualNumber Λ k) (origin G x0) (origin G x0)

/-- The underlying arrow of an infinitesimal automorphism of `[U/R]`. -/
def infAutQuotient_arrow (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x0 : G.U.obj (residue Λ k)) (p : infAutQuotient G x0) : G.R.obj (dualNumber Λ k) :=
  p.arrow

/-- Membership in `infAutQuotient` is the equalizer condition `s(r) = t(r) = origin`. -/
theorem infAutQuotient_iff (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x0 : G.U.obj (residue Λ k)) (p : infAutQuotient G x0) :
    G.s.app (dualNumber Λ k) (infAutQuotient_arrow G x0 p) = origin G x0 ∧
      G.t.app (dualNumber Λ k) (infAutQuotient_arrow G x0 p) = origin G x0 := sorry

/-- Lemma 90.24.2 (3): the space of infinitesimal automorphisms of `[U/R]` is
`Inf([U/R]) = Ker(ds ⊕ dt : TR → TU ⊕ TU)`. This kernel consists of arrows of `R` at
`dualNumber Λ k` with source and target equal to the origin of `U`. -/
@[stacks 06KU]
def infinitesimalAutomorphisms_quotient
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x0 : G.U.obj (residue Λ k)) :
    infAutQuotient G x0 ≃
      { r : G.R.obj (dualNumber Λ k) //
          G.s.app (dualNumber Λ k) r = origin G x0 ∧
            G.t.app (dualNumber Λ k) r = origin G x0 } where
  toFun p := ⟨p.arrow, p.source, p.target⟩
  invFun := fun ⟨r, hs, ht⟩ ↦ PointHom.ofArrow r hs ht
  left_inv := sorry
  right_inv := sorry

/-- The forward comparison of `infinitesimalAutomorphisms_quotient` is the underlying arrow. -/
theorem infinitesimalAutomorphisms_quotient_apply
    (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.U)]
    [Functor.IsDeformationCategory (CategoryOfElements.π G.R)]
    (x0 : G.U.obj (residue Λ k)) (p : infAutQuotient G x0) :
    Subtype.val (infinitesimalAutomorphisms_quotient G x0 p) =
      infAutQuotient_arrow G x0 p := sorry

end CategoryTheory.GroupoidInFunctors
