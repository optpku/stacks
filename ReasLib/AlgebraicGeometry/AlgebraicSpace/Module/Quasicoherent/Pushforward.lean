module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Quasi-coherent pushforward on algebraic spaces

Along a quasi-compact and quasi-separated morphism of algebraic spaces, module
pushforward preserves quasi-coherence and therefore restricts to a functor
`QCoh X ⥤ QCoh Y`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

namespace QCoh

/-- The object-property premise that a morphism of algebraic spaces preserves
quasi-coherent modules. -/
abbrev preservesQuasiCoherent (f : X ⟶ Y) : Prop :=
  quasiCoherentModuleProperty X ≤
    (quasiCoherentModuleProperty Y).inverseImage (Modules.pushforward f)

namespace pushforward

/-- Qcqs pushforward carries quasi-coherent modules to quasi-coherent modules. -/
theorem mapsTo (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    preservesQuasiCoherent f :=
  sorry

end pushforward

/-- Pushforward along a qcqs morphism, restricted to quasi-coherent modules. -/
noncomputable def pushforward (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    QCoh X ⥤ QCoh Y :=
  FullSubcategory.restrict (Modules.pushforward f) (pushforward.mapsTo f)

/-- Forgetting quasi-coherence after restricted pushforward recovers ambient
module-sheaf pushforward. -/
noncomputable def pushforward.inclusionIso
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pushforward f ⋙ inclusion Y ≅ inclusion X ⋙ Modules.pushforward f :=
  FullSubcategory.restrict.compιIso (Modules.pushforward f) (pushforward.mapsTo f)

namespace pushforward

/-- The underlying module sheaf of quasi-coherent pushforward is ambient
module-sheaf pushforward. -/
@[simp]
theorem obj_obj (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (F : QCoh X) :
    ((pushforward f).obj F).obj = (Modules.pushforward f).obj F.obj :=
  rfl

/-- The underlying morphism of quasi-coherent pushforward is the ambient
pushforward of the underlying morphism. -/
@[simp]
theorem map_hom (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {F G : QCoh X} (phi : F ⟶ G) :
    ((pushforward f).map phi).hom = (Modules.pushforward f).map phi.hom :=
  rfl

end pushforward

end QCoh

namespace Modules

namespace pushforward

/-- Pushforward along a quasi-compact and quasi-separated morphism of algebraic
spaces preserves quasi-coherent modules. -/
instance isQuasicoherent (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).IsQuasicoherent :=
  QCoh.pushforward.mapsTo f F inferInstance

/-- Explicit-hypothesis form of qcqs pushforward preserving quasi-coherence. -/
theorem isQuasicoherentOf (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {F : X.Modules} (hF : F.IsQuasicoherent) :
    ((pushforward f).obj F).IsQuasicoherent :=
  QCoh.pushforward.mapsTo f F hF

end pushforward

end Modules

end AlgebraicGeometry.AlgebraicSpace
