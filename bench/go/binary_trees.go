// binary-trees, single-threaded: allocation and freeing of many small trees.
package main
import ("fmt"; "os"; "strconv")
type Node struct{ l, r *Node }
func make_(d int) *Node { if d > 0 { return &Node{make_(d - 1), make_(d - 1)} }; return &Node{} }
func check(n *Node) int { if n.l != nil { return 1 + check(n.l) + check(n.r) }; return 1 }
func main() {
	n := 10; if len(os.Args) > 1 { n, _ = strconv.Atoi(os.Args[1]) }
	max := n; if max < 6 { max = 6 }
	fmt.Printf("stretch tree of depth %d\t check: %d\n", max+1, check(make_(max+1)))
	long := make_(max)
	for d := 4; d <= max; d += 2 {
		iters := 1 << (max - d + 4); sum := 0
		for i := 0; i < iters; i++ { sum += check(make_(d)) }
		fmt.Printf("%d\t trees of depth %d\t check: %d\n", iters, d, sum)
	}
	fmt.Printf("long lived tree of depth %d\t check: %d\n", max, check(long))
}
