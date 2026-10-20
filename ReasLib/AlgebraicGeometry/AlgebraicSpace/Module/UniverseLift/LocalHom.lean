module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-!
# Local morphisms before and after universe lift

A local section of the universe-lifted internal Hom is an actual morphism on the slice site.
Its component functions lower by `ULift.down`; the reverse construction applies `ULift.up`
after the given component function. Thus a local parameter can be used on the original module
carriers without selecting a morphism from an existence assertion.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (F G : X.Modules) (T : smallEtaleSite X)

/-- Lower a local morphism of the lifted module sheaves by applying its actual component map
to `ULift.up x` and reading the result with `ULift.down`. -/
def lowerLocalHom
    (θ : InternalHom.LocalHom.{u + 1, u, u + 1} (commStructureSheafLift X) (liftModule (X := X) F) (liftModule (X := X) G)
      (op T)) : F.over T ⟶ G.over T :=
  ⟨{
    app := fun V ↦ ModuleCat.ofHom
        (X := (F.over T).val.obj V) (Y := (G.over T).val.obj V)
        { toFun := fun x ↦ ((θ.val.app V).hom (ULift.up x)).down
          map_add' := sorry
          map_smul' := sorry }
    naturality := sorry }⟩

/-- Lift a local morphism by applying its supplied component map to `ULift.down x` and
returning `ULift.up` of the result. -/
def liftLocalHom (θ : F.over T ⟶ G.over T) :
    InternalHom.LocalHom.{u + 1, u, u + 1} (commStructureSheafLift X) (liftModule (X := X) F) (liftModule (X := X) G) (op T) :=
  ⟨{
    app := fun V ↦ ModuleCat.ofHom
        (X := ((liftModule (X := X) F).over T).val.obj V)
        (Y := ((liftModule (X := X) G).over T).val.obj V)
        { toFun := fun x ↦ ULift.up ((θ.val.app V).hom x.down)
          map_add' := sorry
          map_smul' := sorry }
    naturality := sorry }⟩

/-- The component of lowering a local parameter is the actual downward-lift formula. -/
@[simp]
theorem lowerLocalHom_apply
    (θ : InternalHom.LocalHom.{u + 1, u, u + 1} (commStructureSheafLift X) (liftModule (X := X) F) (liftModule (X := X) G)
      (op T)) (V : (Over T)ᵒᵖ) (x : (F.over T).val.obj V) :
    ((lowerLocalHom (X := X) F G T θ).val.app V).hom x =
      ((θ.val.app V).hom (ULift.up x)).down := rfl

/-- The component of lifting a local morphism is the actual upward-lift formula. -/
@[simp]
theorem liftLocalHom_apply (θ : F.over T ⟶ G.over T) (V : (Over T)ᵒᵖ)
    (x : ((liftModule (X := X) F).over T).val.obj V) :
    ((liftLocalHom (X := X) F G T θ).val.app V).hom x =
      ULift.up ((θ.val.app V).hom x.down) := rfl

/-- Universe lifting and lowering recover the supplied local module morphism. -/
theorem lowerLocalHom_liftLocalHom (θ : F.over T ⟶ G.over T) :
    lowerLocalHom (X := X) F G T (liftLocalHom (X := X) F G T θ) = θ := sorry

/-- Lowering and lifting recover the supplied local morphism of lifted modules. -/
theorem liftLocalHom_lowerLocalHom
    (θ : InternalHom.LocalHom.{u + 1, u, u + 1} (commStructureSheafLift X) (liftModule (X := X) F) (liftModule (X := X) G)
      (op T)) :
    liftLocalHom (X := X) F G T (lowerLocalHom (X := X) F G T θ) = θ := sorry

/-- Internal-Hom sections and local morphisms on the original modules have specified maps
in both directions. -/
def localHomEquiv :
    InternalHom.LocalHom.{u + 1, u, u + 1} (commStructureSheafLift X) (liftModule (X := X) F) (liftModule (X := X) G) (op T) ≃
      (F.over T ⟶ G.over T) where
  toFun := lowerLocalHom (X := X) F G T
  invFun := liftLocalHom (X := X) F G T
  left_inv := liftLocalHom_lowerLocalHom (X := X) F G T
  right_inv := lowerLocalHom_liftLocalHom (X := X) F G T

end AlgebraicGeometry.AlgebraicSpace.Modules
