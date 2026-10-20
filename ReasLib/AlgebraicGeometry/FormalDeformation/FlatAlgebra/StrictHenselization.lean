module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.RingTheory.Henselian.StrictHenselization

/-!
# Strict henselization of flat algebra deformations
-/

@[expose] public section

open CategoryTheory Functor

universe u

namespace FlatAlgebraCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (P : Type u) [CommRing P] [Algebra k P]
variable (Psh : Type u) [CommRing Psh] [Algebra k Psh] [Algebra P Psh]

/-- A functor on deformation categories is a strict henselization functor if it preserves
the Artinian base and admits natural structural maps exhibiting its image algebras as
strict henselizations, compatibly with the base actions and the special-fibre maps. -/
def IsStrictHenselizationFunctor
    (F : deformationCategory Λ k P ⥤ deformationCategory Λ k Psh) : Prop :=
  (F ⋙ Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k Psh)) ⋙
      (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) =
    Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙
      (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)) ∧
  ∃ ι : ∀ ξ : deformationCategory Λ k P, ξ.left.algebra →+* (F.obj ξ).left.algebra,
    (∀ ξ, ∃ (hbase : (F.obj ξ).left.base = ξ.left.base)
        (hlocal : IsLocalRing ξ.left.algebra),
      (∀ a : (F.obj ξ).left.base.carrier,
        ι ξ (algebraMap ξ.left.base.carrier ξ.left.algebra
          (Eq.mp (congrArg (fun B : ArtinianLocalAlgCat Λ k => (B.carrier : Type u))
            hbase) a)) =
          algebraMap (F.obj ξ).left.base.carrier (F.obj ξ).left.algebra a) ∧
      @IsStrictHenselizationOf ξ.left.algebra _ hlocal (F.obj ξ).left.algebra _
        (ι ξ).toAlgebra ∧
      (F.obj ξ).hom.toRingHom.comp (ι ξ) =
        (algebraMap P Psh).comp ξ.hom.toRingHom) ∧
    ∀ (ξ η : deformationCategory Λ k P) (f : ξ ⟶ η),
      (F.map f).left.toRingHom.comp (ι ξ) = (ι η).comp f.left.toRingHom

namespace IsStrictHenselizationFunctor

variable {Λ k P Psh}
variable {F : deformationCategory Λ k P ⥤ deformationCategory Λ k Psh}

/-- A strict henselization functor commutes with the projections to the Artinian base. -/
theorem comp_forget (hF : IsStrictHenselizationFunctor Λ k P Psh F) :
    F ⋙ Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k Psh)) ⋙
        (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙
        (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) :=
  hF.1

/-- A strict henselization functor admits natural structural maps that respect the
Artinian-base actions and special-fibre maps and exhibit strict henselizations. -/
theorem exists_lifts (hF : IsStrictHenselizationFunctor Λ k P Psh F) :
    ∃ ι : ∀ ξ : deformationCategory Λ k P, ξ.left.algebra →+* (F.obj ξ).left.algebra,
      (∀ ξ, ∃ (hbase : (F.obj ξ).left.base = ξ.left.base)
          (hlocal : IsLocalRing ξ.left.algebra),
        (∀ a : (F.obj ξ).left.base.carrier,
          ι ξ (algebraMap ξ.left.base.carrier ξ.left.algebra
            (Eq.mp (congrArg (fun B : ArtinianLocalAlgCat Λ k => (B.carrier : Type u))
              hbase) a)) =
            algebraMap (F.obj ξ).left.base.carrier (F.obj ξ).left.algebra a) ∧
        @IsStrictHenselizationOf ξ.left.algebra _ hlocal (F.obj ξ).left.algebra _
          (ι ξ).toAlgebra ∧
        (F.obj ξ).hom.toRingHom.comp (ι ξ) =
          (algebraMap P Psh).comp ξ.hom.toRingHom) ∧
      ∀ (ξ η : deformationCategory Λ k P) (f : ξ ⟶ η),
        (F.map f).left.toRingHom.comp (ι ξ) = (ι η).comp f.left.toRingHom :=
  hF.2

end IsStrictHenselizationFunctor

/-- A strict henselization of a local residue-field algebra induces a functor on its
flat deformation category, preserving the Artinian base and naturally replacing each
deformation algebra by a strict henselization compatible with the special fibre. -/
theorem exists_strictHenselizationFunctor [IsLocalRing P] [IsScalarTower k P Psh]
    [IsStrictHenselizationOf P Psh] :
    ∃ F : deformationCategory Λ k P ⥤ deformationCategory Λ k Psh,
      IsStrictHenselizationFunctor Λ k P Psh F := by
  sorry

end FlatAlgebraCat
