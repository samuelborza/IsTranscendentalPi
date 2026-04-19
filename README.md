# IsTranscendentalPi

Formalization in Lean of the transcendence of `π`.

The main results are in [IsTranscendentalPi/Main.lean](IsTranscendentalPi/Main.lean):

- `IsTranscendentalPi : Transcendental ℚ (Real.pi : ℂ)`
- `IsTranscendentalPiReal : Transcendental ℚ (Real.pi : ℝ)`

## Build

```sh
lake build
```

## File structure

- `IsTranscendentalPi/IncrementalDerivatives.lean`
- `IsTranscendentalPi/ComplexExponential.lean`
- `IsTranscendentalPi/CalculusOnPoly.lean`
- `IsTranscendentalPi/NivenPolynomials.lean`
- `IsTranscendentalPi/SymmetricPolynomials.lean`
- `IsTranscendentalPi/SubsetSumPolynomial.lean`
- `IsTranscendentalPi/ScaledAuxiliaryPolynomial.lean`
- `IsTranscendentalPi/AnalyticEstimates.lean`
- `IsTranscendentalPi/Main.lean`

## Dependencies

This project uses:

- Lean 4
- mathlib

The exact toolchain is pinned in `lean-toolchain`.
