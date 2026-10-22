// spectral-norm: the largest eigenvalue of an infinite matrix, by the power method; floating point
// loops over arrays.
package main
import ("fmt"; "math"; "os"; "strconv")
func a(i, j int) float64 { return 1.0 / float64((i+j)*(i+j+1)/2+i+1) }
func mulAv(v, av []float64) { for i := range av { s := 0.0; for j, x := range v { s += a(i, j) * x }; av[i] = s } }
func mulAtv(v, atv []float64) { for i := range atv { s := 0.0; for j, x := range v { s += a(j, i) * x }; atv[i] = s } }
func main() {
	n := 100; if len(os.Args) > 1 { n, _ = strconv.Atoi(os.Args[1]) }
	u, v, tmp := make([]float64, n), make([]float64, n), make([]float64, n)
	for i := range u { u[i] = 1 }
	for i := 0; i < 10; i++ { mulAv(u, tmp); mulAtv(tmp, v); mulAv(v, tmp); mulAtv(tmp, u) }
	var vBv, vv float64
	for i := range u { vBv += u[i] * v[i]; vv += v[i] * v[i] }
	fmt.Printf("%.9f\n", math.Sqrt(vBv/vv))
}
