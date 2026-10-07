module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.RingTheory.Henselian
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Henselian local rings of decent algebraic spaces

The henselian local ring of a decent algebraic space `X` at a point `x ∈ |X|` is the
colimit of the global-section rings `Γ(U, 𝒪_U)` indexed by elementary étale
neighbourhoods `(U, u) ⟶ (X, x)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary

/-- The functor sending an elementary étale neighbourhood of `(X, x)` to its underlying
scheme. -/
def toScheme {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    Elementary X x ⥤ Scheme.{u} :=
  ObjectProperty.ι (fun U : EtaleNeighborhood X x ↦ U.IsElementary) ⋙
    CategoryOfElements.π (pointFiber x) ⋙ smallEtaleToScheme X

/-- The object action of `toScheme` forgets to the scheme underlying an elementary étale
neighbourhood. -/
@[simp]
theorem toScheme_obj {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X)
    (U : Elementary X x) : (toScheme X x).obj U = U.obj.scheme :=
  sorry

/-- The morphism action of `toScheme` forgets to the underlying scheme morphism. -/
@[simp]
theorem toScheme_map {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X)
    {U V : Elementary X x} (f : U ⟶ V) :
    (toScheme X x).map f = Hom.schemeHom f :=
  sorry

/-- The diagram of global-section rings of elementary étale neighbourhoods, with hom
universes and section rings lifted to a common universe. -/
def sections {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    ULiftHom.{u + 1} ((Elementary X x)ᵒᵖ) ⥤ CommRingCat.{u + 1} :=
  ULiftHom.down ⋙ (toScheme X x).op ⋙ Scheme.Γ ⋙ CommRingCat.universeLift.{u, u + 1}

/-- At an elementary étale neighbourhood `U`, the sections diagram is the universe lift of
`Γ((toScheme X x).obj U, ⊤)`. -/
theorem sections_obj {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X)
    (U : Elementary X x) :
    (sections X x).obj (ULiftHom.objUp (op U)) =
      (CommRingCat.universeLift.{u, u + 1}).obj
        (Scheme.Γ.obj (op ((toScheme X x).obj U))) :=
  sorry

/-- A pointed map `U ⟶ V` induces the contravariant restriction map from the section ring
of `V` to that of `U`. -/
theorem sections_map {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X)
    {U V : Elementary X x} (f : U ⟶ V) :
    (sections X x).map (ULiftHom.up.map f.op) =
      (CommRingCat.universeLift.{u, u + 1}).map (Scheme.Γ.map (Hom.schemeHom f).op) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary

namespace AlgebraicGeometry.AlgebraicSpace

/-- The colimit of global-section rings of elementary étale neighbourhoods, as an object
of `CommRingCat`. -/
noncomputable def henselianLocalRingCat {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) : CommRingCat.{u + 1} :=
  colimit (EtaleNeighborhood.Elementary.sections X x)

/-- `henselianLocalRingCat X x` is the colimit of the sections diagram in `CommRingCat`. -/
theorem henselianLocalRingCat_eq {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    henselianLocalRingCat X x = colimit (EtaleNeighborhood.Elementary.sections X x) :=
  sorry

/-- The henselian local ring of a decent algebraic space `X` at a point `x ∈ |X|` is the
colimit of `Γ(U, 𝒪_U)` over elementary étale neighbourhoods `(U, u) ⟶ (X, x)`. -/
noncomputable def henselianLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Type (u + 1) :=
  henselianLocalRingCat X x

/-- `henselianLocalRing X x` is the carrier of `henselianLocalRingCat X x`. -/
theorem henselianLocalRing_def {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    henselianLocalRing X x = (henselianLocalRingCat X x : Type (u + 1)) :=
  sorry

/-- The colimit of global sections of elementary étale neighbourhoods is a commutative
ring. -/
instance henselianLocalRing.instCommRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) : CommRing (henselianLocalRing X x) :=
  inferInstanceAs (CommRing (henselianLocalRingCat X x : Type (u + 1)))

/-- The henselian local ring of a decent algebraic space is a henselian local ring. -/
instance henselianLocalRing.instHenselianLocalRing {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    HenselianLocalRing (henselianLocalRing X x) :=
  sorry

/-- The canonical map from global sections of an elementary étale neighbourhood into the
henselian local ring, as the coprojection of the defining colimit. -/
noncomputable def henselianLocalRing.ι {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) (U : EtaleNeighborhood.Elementary X x) :
    Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) →+* henselianLocalRing X x :=
  (colimit.ι (EtaleNeighborhood.Elementary.sections X x) (ULiftHom.objUp (op U))).hom.comp
    (ULift.ringEquiv.symm :
        Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) ≃+*
          ULift.{u + 1} Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤)).toRingHom

/-- `henselianLocalRing.ι` is the colimit coprojection after the universe lift of global
sections. -/
theorem henselianLocalRing.ι_def {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) (U : EtaleNeighborhood.Elementary X x) :
    henselianLocalRing.ι X x U =
      (colimit.ι (EtaleNeighborhood.Elementary.sections X x)
          (ULiftHom.objUp (op U))).hom.comp
        (ULift.ringEquiv.symm :
            Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤) ≃+*
              ULift.{u + 1}
                Γ((EtaleNeighborhood.Elementary.toScheme X x).obj U, ⊤)).toRingHom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
