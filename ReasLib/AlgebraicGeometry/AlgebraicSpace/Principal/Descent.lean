module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Torsor.Descent

/-!
# Descent of principal homogeneous spaces

Explicit equivariant cocycle data for principal homogeneous spaces on an fppf
covering, together with global realizations recovering the full overlap data.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupAlgebraicSpace.Principal

variable {U : Scheme.{u}} {I : Type v} (Ui : I → Over U)
variable (H : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 U))))

/-- Descent data for principal homogeneous spaces under a group algebraic space
along an fppf covering of schemes. -/
structure DescentDatum where
  /-- The family `{U_i → U}` is an fppf covering. -/
  covering : Scheme.FppfCovering Ui
  /-- The local `H_{U_i}`-actions `X_i` over `U_i`. -/
  obj : ∀ i, Action (baseChange H (SchemeRealization.toBase (ofOver (Ui i))))
  /-- Each `X_i` is a principal homogeneous `H_{U_i}`-space. -/
  isPrincipal : ∀ i, IsTorsor (baseChange H (SchemeRealization.toBase (ofOver (Ui i)))) (obj i)
  /-- The `H_{U_i ×_U U_j}`-equivariant isomorphisms
  `φ_ij : X_i ×_U U_j ≅ U_i ×_U X_j`. -/
  iso : ∀ i j, Torsor.leftRestrict Ui H i j (obj i) ≅ Torsor.rightRestrict Ui H i j (obj j)
  /-- The family `φ_ij` satisfies the cocycle condition on every
  `U_i ×_U U_j ×_U U_k`. -/
  cocycle : Torsor.IsCocycle Ui H obj iso

namespace DescentDatum

/-- Assemble descent data from an fppf covering, local principal homogeneous
spaces, equivariant overlap isomorphisms, and the cocycle condition. -/
def ofIso (covering : Scheme.FppfCovering Ui)
    (obj : ∀ i, Action (baseChange H (SchemeRealization.toBase (ofOver (Ui i)))))
    (isPrincipal : ∀ i, IsTorsor (baseChange H (SchemeRealization.toBase (ofOver (Ui i)))) (obj i))
    (iso : ∀ i j, Torsor.leftRestrict Ui H i j (obj i) ≅ Torsor.rightRestrict Ui H i j (obj j))
    (cocycle : Torsor.IsCocycle Ui H obj iso) : DescentDatum Ui H where
  covering := covering
  obj := obj
  isPrincipal := isPrincipal
  iso := iso
  cocycle := cocycle

/-- The constructor `ofIso` stores the supplied covering and local actions. -/
theorem ofIso_spec (covering : Scheme.FppfCovering Ui)
    (obj : ∀ i, Action (baseChange H (SchemeRealization.toBase (ofOver (Ui i)))))
    (isPrincipal : ∀ i, IsTorsor (baseChange H (SchemeRealization.toBase (ofOver (Ui i)))) (obj i))
    (iso : ∀ i j, Torsor.leftRestrict Ui H i j (obj i) ≅ Torsor.rightRestrict Ui H i j (obj j))
    (cocycle : Torsor.IsCocycle Ui H obj iso) :
    (ofIso Ui H covering obj isPrincipal iso cocycle).covering = covering ∧
      (ofIso Ui H covering obj isPrincipal iso cocycle).obj = obj := ⟨rfl, rfl⟩

/-- The overlap isomorphisms stored by `ofIso` are the supplied family `φ_ij`. -/
theorem ofIso_iso (covering : Scheme.FppfCovering Ui)
    (obj : ∀ i, Action (baseChange H (SchemeRealization.toBase (ofOver (Ui i)))))
    (isPrincipal : ∀ i, IsTorsor (baseChange H (SchemeRealization.toBase (ofOver (Ui i)))) (obj i))
    (iso : ∀ i j, Torsor.leftRestrict Ui H i j (obj i) ≅ Torsor.rightRestrict Ui H i j (obj j))
    (cocycle : Torsor.IsCocycle Ui H obj iso) :
    (ofIso Ui H covering obj isPrincipal iso cocycle).iso = iso := rfl

/-- Base change of a principal homogeneous space to each member of a covering
is again a principal homogeneous space. -/
theorem ofTorsor_isPrincipal (X : Action H) (hX : IsTorsor H X) (i : I) :
    IsTorsor (baseChange H (SchemeRealization.toBase (ofOver (Ui i))))
      (pullbackAction (SchemeRealization.toBase (ofOver (Ui i))) H X) := sorry

/-- The canonical overlap comparisons of a global action satisfy the cocycle
condition on triple overlaps. -/
theorem ofTorsor_cocycle (X : Action H) :
    Torsor.IsCocycle Ui H
      (fun i ↦ pullbackAction (SchemeRealization.toBase (ofOver (Ui i))) H X)
      (fun i j ↦ Torsor.canonicalOverlap Ui H X i j) := sorry

/-- Canonical descent data of a global principal homogeneous `H`-space along an
fppf covering. -/
def ofTorsor (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) : DescentDatum Ui H where
  covering := hUi
  obj := fun i ↦ pullbackAction (SchemeRealization.toBase (ofOver (Ui i))) H X
  isPrincipal := ofTorsor_isPrincipal Ui H X hX
  iso := fun i j ↦ Torsor.canonicalOverlap Ui H X i j
  cocycle := ofTorsor_cocycle Ui H X

/-- The local objects of `ofTorsor` are the slice pullbacks of the global
action. -/
theorem ofTorsor_obj (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) (i : I) :
    (ofTorsor Ui H hUi X hX).obj i = pullbackAction (SchemeRealization.toBase (ofOver (Ui i))) H X := rfl

/-- The covering stored by `ofTorsor` is the supplied fppf covering. -/
theorem ofTorsor_covering (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) :
    (ofTorsor Ui H hUi X hX).covering = hUi := rfl

/-- The overlap isomorphisms of `ofTorsor` are the canonical pullback
comparisons of `X`. -/
theorem ofTorsor_iso (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) (i j : I) :
    (ofTorsor Ui H hUi X hX).iso i j = Torsor.canonicalOverlap Ui H X i j := rfl

/-- An effective realisation of descent data: a global principal homogeneous
`H`-space whose base changes recover the local spaces and the descent
isomorphisms `φ_ij`. -/
structure Effectiveness (D : DescentDatum Ui H) where
  /-- The global `H`-action over `U`. -/
  X : Action H
  /-- The global action is a principal homogeneous `H`-space. -/
  isPrincipal : IsTorsor H X
  /-- Base change of `X` to each `U_i` recovers `X_i`. -/
  iso : ∀ i, pullbackAction (SchemeRealization.toBase (ofOver (Ui i))) H X ≅ D.obj i
  /-- The descent isomorphisms `φ_ij` are the comparisons of the base-change
  isomorphisms of `X`. -/
  recovers : ∀ i j,
    Torsor.leftRestrict_mapIso Ui H i j (iso i) ≪≫ D.iso i j =
      Torsor.canonicalOverlap Ui H X i j ≪≫ Torsor.rightRestrict_mapIso Ui H i j (iso j)

/-- Identity local identifications recover the canonical overlap comparisons
of a global principal homogeneous space. -/
theorem Effectiveness.ofTorsor_recovers (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) :
    ∀ i j,
      Torsor.leftRestrict_mapIso Ui H i j
          (Iso.refl (pullbackAction (SchemeRealization.toBase (ofOver (Ui i))) H X)) ≪≫
          (ofTorsor Ui H hUi X hX).iso i j =
        Torsor.canonicalOverlap Ui H X i j ≪≫
          Torsor.rightRestrict_mapIso Ui H i j
            (Iso.refl (pullbackAction (SchemeRealization.toBase (ofOver (Ui j))) H X)) := sorry

/-- The identity datum of a global principal homogeneous `H`-space is effective,
realised by that same space. -/
def Effectiveness.ofTorsor (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) :
    (ofTorsor Ui H hUi X hX).Effectiveness where
  X := X
  isPrincipal := hX
  iso := fun i ↦ Iso.refl (pullbackAction (SchemeRealization.toBase (ofOver (Ui i))) H X)
  recovers := Effectiveness.ofTorsor_recovers Ui H hUi X hX

/-- The global action stored by `Effectiveness.ofTorsor` is the original
action. -/
theorem Effectiveness.ofTorsor_X (hUi : Scheme.FppfCovering Ui) (X : Action H)
    (hX : IsTorsor H X) :
    (Effectiveness.ofTorsor Ui H hUi X hX).X = X := rfl

/-- An effective realisation is a principal homogeneous `H`-space whose overlap
comparisons recover `φ_ij`. -/
theorem Effectiveness.spec {D : DescentDatum Ui H} (E : D.Effectiveness) :
    IsTorsor H E.X ∧
      ∀ i j,
        Torsor.leftRestrict_mapIso Ui H i j (E.iso i) ≪≫ D.iso i j =
          Torsor.canonicalOverlap Ui H E.X i j ≪≫
            Torsor.rightRestrict_mapIso Ui H i j (E.iso j) := ⟨E.isPrincipal, E.recovers⟩

/-- Principal homogeneous spaces equipped with equivariant cocycle data descend
along a small fppf covering to a global principal homogeneous space recovering
the supplied local spaces and overlap isomorphisms. -/
theorem exists_principalHomogeneous {U : Scheme.{u}} {I : Type v} [Small.{u} I]
    {Ui : I → Over U} {H : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 U)))}
    (D : DescentDatum Ui H) : Nonempty D.Effectiveness := sorry

end DescentDatum

end AlgebraicGeometry.GroupAlgebraicSpace.Principal

