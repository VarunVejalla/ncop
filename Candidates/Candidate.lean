import NCop.Target
import NCop.Lemmas

/-!
This is the file intended for automated mutation.

The public interface expected by `scripts/evaluate_candidate.py` is:

* `def C1 : ℝ := ...`
* `def C2 : ℝ := ...`
* `theorem lower : NCop.BreakerLowerBound C1 := ...`
* `theorem upper : NCop.MakerUpperBound C2 := ...`

This file currently contains only target constants, not proved endpoints.
The established mathematical baseline is the matroid lower coefficient 2 and
the two-frontier upper coefficient 4; both asymptotic theorems remain to be
formalized. Source isolation is only a weaker preliminary proof target.
-/

namespace Candidate

def C1 : ℝ := 2
def C2 : ℝ := 4

end Candidate
