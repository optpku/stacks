module

public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom

@[expose] public section

namespace RingHom.IsLocalCompleteIntersection

/-- Local complete-intersection ring maps are stable under composition. -/
theorem stableUnderComposition :
    RingHom.StableUnderComposition (@RingHom.IsLocalCompleteIntersection) := sorry

end RingHom.IsLocalCompleteIntersection
