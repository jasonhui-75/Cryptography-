import java.util.*;
import java.util.ArrayList;
import java.lang.Math;

public class CryptographyCalculator {

	public static void main(String[] args) throws Exception {
		// TODO Auto-generated method stub
	
		//ArrayList<Long> input = new ArrayList<>(Arrays.asList((long)2, (long)3, (long)3, (long)7, (long)4, (long)16));
		//System.out.println("crt: "+crt(input));

		//System.out.println("Miller-Rabin(561):" + mrt(561,2));
		//System.out.println("Miller-Rabin(561):" + mrt(172947529,3));
		//System.out.println("Miller-Rabin test (16273):" + mrt75(16273));
		
		System.out.println("Using Pohlig-Hellman to find 23^x = 9689 (mod 11251), and x =" + pha(23, 9689, 11251));
		System.out.println("\nAnother example \n");
		System.out.println("Using Pohlig-Hellman to find 7^x = 166 (mod 433), and x =" + pha(7, 166, 433));
		//System.out.println("pohlig-hellman:" + phaq(7, 166, 433));
		
		//System.out.println("Power Mod:" + powMod(5448, -(1 *1), 11251));
		/*
		 * ArrayList<long[]> i = primePowerFactors(24); String o = new String(); for
		 * (int j = 0; j <i.size(); j++) o += Arrays.toString(i.get(j))+", ";
		 * System.out.println("PPF:" + o);
		 */
		//System.out.println("Seive:" + (sieve(1000)));
		//System.out.println("ord:"+order(13, 23));
		//System.out.println("col:"+collision( 9704, 13896 ,  17389));
		//System.out.println("mod2: " + mod(10,61));
	}
	
	//return m (mod n), where m is an integer and n is a positive integer
	public static long mod(long m, long n) throws Exception
	{
		if (n< 0)
			throw new Exception("Modulus, " + n +", cannot be negative");
		if(m >= 0)
		{
			return m- (m/n)*n;
		}
		else
		{
			// remainder = m - n * floor(m/n)
			return (long) m-(n* (long) Math.floor(((double)m/n)));
		}
		
	}
	//Calculate GCD using the Euclidean algorithm
	public static long euclidean(long v1, long v2) throws Exception
	{
		long a, b;
			a = v1;
			b = v2;
			
		long remainder = mod(a,b);
		//this while loop will run at most log(a) times
		while (remainder != 0)
		{
			remainder = mod(a,b);
			a = b;
			b = remainder;
		}
		return a;
	}
	//Calculate GCD using the extended Euclidean algorithm
	public static long[] exteuclidean(long v1, long v2) throws Exception
	{
		long u =1, g = v1, x =0, y = v2, s;
		//this while loop also runs O(log(y)) times
		while (y != 0)
		{
			long q = g/y, t = mod(g,y);
			s = u - (q) * x;
			u = x;
			g = y;
			x = s;
			y = t;
			
		}
		long v = (g - v1*u)/v2;
		long[] triple = new long[] {g, u, v};
		
		return triple;
		
		
	}
	
	
	
	//Square and multiply algorithm returns g^pow (mod n) in O(log pow)
	public static long sam(long n, long g, long pow)
	{
		long a = g, b = 1, p = pow;
		//this while loop will run log(p) times
		while (p > 0)
		{
			if (p%2 ==1)
			{
				b = (b*a)%n;
			}
			a = (a*a)%n;
			p = p/2;
		}
		return b;
	}
	
	//return the factors of n in O(sqrt n)
	public static ArrayList<Long> factor(long n)
	{
		long i = 2;
		ArrayList<Long> result = new ArrayList<Long>();
		
		while(i <= Math.sqrt(n))
		{
			if(n%i ==0)
			{
				result.add(i);
				if (i != (n/i))
				{
					result.add(n/i);
				}
			}
			i++;
		}
		return result;
	}
	
	//return logb (n)
	public static long logb(long n, long b)
	{
		return (long)(Math.log(n)/ Math.log(2));
		
	}

	public static long pow(long b, long e)
	{
		if (e < 0)
		{
			b = 1/b;
			e = -e;
		}
		else if (e == 0)
			return 1;
		long y = 1;
		while (e > 1)
		{
			if(e%2 == 0)
			{
				b = b*b;
				e = e/2;
			}
			else
			{
				y = b*y;
				b = b*b;
				e = (e-1)/2;
			}
		}
		return b *y;
	}
	
	// compute b^e mod n in O(log e)
	public static long powMod(long b, long e, long n) throws Exception
	{
		boolean neg = false;
		if (e < 0)
		{
			neg = true;
			//b = 1/b;
			e = -e;
		}
		else if (e == 0)
			return 1;
		long y = 1;
		while (e > 1)
		{
			if(e%2 == 0)
			{
				b = mod((b*b),n);
				e = e/2;
			}
			else
			{
				y = mod((b*y),n);
				b = mod((b*b),n);
				e = (e-1)/2;
			}
		}
		if(!neg)
		
			return mod(b *y, n);
		else
			return exteuclidean(mod(b *y, n), n)[1];
	}
	

	public static long order(long m, long n) throws Exception
	{
		//first find and sort all the factors of n-1 < sqrt n.
		ArrayList<Long> fac = factor(n-1);
		Collections.sort(fac);
		//System.out.println(fac.toString());
		//System.out.println(fac.size());
		
		int i = 0;
		while (i < fac.size())
		{
			long factor = powMod(m, fac.get(i), n);
			long res = factor%n;
			if(res == 1)
				return fac.get(i);
			i++;
		}
		
		return n-1;
	}

	//Shank's babystep-giantstep algorithm
	public static long collision(long g, long h, long p) throws Exception
	//returns true if int a is a Miller-Rabin witness for integer n. Else false if inconclusive.
	
	{
		if (g == h)
			return 1;
		long ord = order(g,p);
		long n = (long) Math.floor(Math.sqrt(ord)) + 1;
	
		ArrayList<Long> gk = new ArrayList<>();
		Map<Long, Long> huk = new HashMap<Long, Long>();
		long i;
		for(i = 0; i <= n; i++)
		{
			gk.add(powMod(g,i,p));
			long u = powMod(g, n, p);
					
			u = exteuclidean(u, p)[1];
			u = powMod(u,i,p);
			huk.put(mod(h* u, p), i);
			
		}
		System.out.println("g^k: "+gk.toString());
		System.out.println("h*u^k: "+huk.toString());
		long x = -1;
		for (int j = 0; j <= n; j++)
		{
			if(huk.containsKey(gk.get(j)))
			{
				x = j + huk.get(gk.get(j))*n;
			}
		}
		return x;
	}
	
	//The Chinese remainder theorem takes an input in the form of [a,m,b,n...] and return x = a (mod m), x = b (mod n)...
	public static long crt(ArrayList<Long> input) throws Exception
		{
			//Print out input first
			String out = new String();
			for (int j = 0; j <input.size(); j+=2)
			{
				if(j != input.size()-1)
					out += "x = "+ input.get(j)+"(mod "+input.get(j+1)+")"+", " ;
				else
					out += "x = "+ input.get(j)+"(mod "+input.get(j+1)+")"+".";
			}
			System.out.println("Using the Chinese Remainder Theorem to solve "+ out);
			long a = input.get(0), m = input.get(1), b = input.get(2), n = input.get(3);
				
				long mc = mod(exteuclidean(m,n)[1],n);
				
				long z = mod((b-a), n);
			
				long c = mod(z*mc, n);
			
				
				long x = mod(a +c*m ,(m*n));
				
				if(input.size() == 4)
					return x;
				else
				{
					//System.out.println("x: "+x);
					ArrayList<Long> i = new ArrayList<>(Arrays.asList(x, (m*n)));
					i.addAll(input.subList(4, input.size()));
					return crt(i);
				}
			//if(input.size() == 4)
			
		}
	
	//returns the list of prime factors and their exponent of c.
	public static ArrayList<long[]> primePowerFactors(long n)
	{
		
		ArrayList<Long> prime = sieve(n);//get the list of prime < n
		ArrayList<long[]> fac = new ArrayList<>(); // list of prime factors
		long comp = n;
		long fi = -1;
		//find the prime power factorization of the order
		for(long p = 0; p < prime.size(); p++)
		{
			
			if(comp%prime.get((int)p) == 0)
			{
				fi++; //index of fac
				fac.add((int)fi,new long[] {prime.get((int)p), 1} );
				comp /= prime.get((int)p);
				
				while(comp%prime.get((int)p) == 0)// while order = 0 (mod p)
				{
					Long e = fac.get((int) fi)[1];
					fac.set((int) fi, new long[] {prime.get((int)p), e+1});
					
					//System.out.println("insert p and "+factors.get(prime.get((int)p)) +", ord: "+ord);
					comp /= prime.get((int)p);
					if(comp <=0)
						break;
				}
			}
			if(comp <=0)
				break;
		}
		//System.out.println("Prime power factors of "+c +"are "+fac.toString());
		return fac;
	}
	
	//Pohlig-Hellman algorithm for g with order n where n can be factored in into q1^e1 *q2^e2...
	//Return integer x where g^x = h (mod n)
	public static long pha(long g, long h, long n) throws Exception
	{
		System.out.println("Step 1");
		//find prime factors of N or the order of g. 
		long order = order(g, n);//this order will not be modified
		System.out.println("The order of  "+g +" is "+order);
		ArrayList<long[]> fac = primePowerFactors(order);
		//This for loop below is to print out the factor and exponent 
		String out = new String();
		for (int j = 0; j <fac.size(); j++)
		{
			if(j != fac.size()-1)
				out += Arrays.toString(fac.get(j))+", ";
			else
				out += Arrays.toString(fac.get(j))+".";
		}
		System.out.println("Prime power factors of "+order +" are "+out);
		ArrayList<Long> gi = new ArrayList<>(); //list of g^((p-1)/q^e)
		ArrayList<Long> hi = new ArrayList<>();//list of h^((p-1)/q^e)
		ArrayList<Long> xi = new ArrayList<>(); //list of x where gi^x = hi
		ArrayList<Long> chinese = new ArrayList<>(); //List of congruence to solve
		System.out.println("Each line below represents (g^(N/q^e))^x = h^(N/q^e) (mod n), where N is the order of g");
		for(int i = 0; i < fac.size();i++)
		{
			long qe = pow(fac.get(i)[0], fac.get(i)[1]);// q^e where q is the prime factor and e is the exponent
			long oq = order/ qe;//order/q^e
			gi.add(powMod(g, oq, n));
			hi.add(powMod(h, oq, n));
			//xi.add(collision(gi.get(i), hi.get(i), n));
			xi.add(phaq(gi.get(i), hi.get(i), n));
			chinese.add(xi.get(i));
			chinese.add(qe);
			System.out.println(g+"^("+order+"/"+qe+"))^"+xi.get(i)+" = "+h+ "^(" + order+"/"+qe+")");
		}
		
		
		System.out.println("Step 2: Use the Chinese Remainder Theorem.");
		return crt(chinese);
	}
	
	//Pohlig-Hellman algorithm for g with order q^e where q is a prime
	public static long phaq(long g, long h, long n) throws Exception 
	{
		long order = order(g, n);//this order will not be modified
		
		ArrayList<long[]> fac = primePowerFactors(order);
		long q = fac.get(0)[0];
		long e = fac.get(0)[1];
		
		long x = 0;
		ArrayList<Long> xi = new ArrayList<>(); //list of x where gi^x = hi
		long gi = powMod(g, pow(q, e-1), n); // g^q^(e-1)
		for(long i = 0; i <e; i++)
		{
			long qe = pow(q, e-(i+1));// qe = q^e-1
			long hi = h;
			long newG = 1;
			for(long index = 0; index < xi.size();index++)
			{
				
				long newQe = pow(q,index);
				newG *= powMod(g, -(xi.get((int)index) *newQe), n);// each iteration g multiplies g^-xi
				
				;
			}
			hi =mod(h* newG,n);// h*g^
			hi = powMod(hi, qe, n);
			for(long ei = 0; ei<= q; ei++)
			{
				long fg = powMod(gi, ei, n);
			
				if( fg == hi)
				{
					xi.add(ei);
				
					break;
				}
			}
			// xi.add(collision(gi,hi, n));
			
			x+=xi.get((int) i)*pow(q,i);
		}
		//System.out.println(xi.toString());
		return x;
	
	}
	
	
	
	//Return true if a is a Miller-Rabin witness for n. Else return false if inconclusive. The time complexity of this algorithm is O(log^3(n))
	public static boolean mrt(long n, long a) throws Exception
	{
		long aValue = a;
		long g = euclidean(a, n); // g = gcd(a,n)
		if(n%2==0 || (g <n && 1 < g))
			return true;
		long k, q =0;
		//this for loop runs log2(n) times and this dominates the running time. 
		for(k = 1; k <= logb(n-1,2);k++)
		{
			//System.out.println("log2 n-1: "+logb(n-1,2));
			long k2 = pow((long)2,k); // k2 = 2^k
			//System.out.println("2^"+k+": "+ k2);
			long n1 = n-1;
			if((n1)%k2 ==0) //checks if 2^k | n-1
			{
				//System.out.println("n-1: "+ n1 +" mod2: "+ n1/2);
				q = (n-1)/k2;
				if (q%2 != 0)//if q is odd then break
				{
					break;
				}
			}
		}
		

		//aValue = sam(aValue, q, n);
		aValue = powMod(aValue, q, n);
		System.out.println("a^q ="+a+"^"+q+" (mod n): "+aValue +", k: "+k);
		if(aValue%n ==1)
			return false;
		for(int i = 0; i <= k-1; i++)
		{
			if(aValue%n == n-1)
				return false;
			System.out.println("a^"+pow(2,i)+"=x(mod n) ="+aValue+"(mod"+n+" )");
			aValue = powMod(aValue, 2, n);
		}
		return true;
	}
	
	//Returns true if n is a composite. This relies on the fact that 75% of the numbers 1 <= a <= n-1 are Miller-Rabin witness for n 
	//The time complexity is O(3/4 n)*O(log^3 n) = O(n log (n)), this trade off ensure this algorithm to always return the correct answer.
	public static boolean mrt75(long n) throws Exception
	{
		long i, n75 = (long) Math.ceil((n-1)*.75); // 
		for (i  = 0; i <= n75 && 2+i < n-1; i++)
		{
			if(mrt(n, 2+i) == true)
				return true;
		}
		return false;
	}
	
	//this is the same as the Miller-Rabin test written above except it uses the fact that if the generalized Reimann hypothesis is true, then every n has a Miller-Rabin witness a satisfying a<= 2(ln n)^2
	//The time complexity for this becomes O(log^2 n) *O(log^3 n) = O (log^5 n)
	public static boolean mrtRei(long n) throws Exception
	{
		long i, n75 = (long) Math.ceil((n-1)*.75); // 
		for (i  = 2; i-2 <= n75 && i < n-1 &&  i < 2*(pow((long)Math.log(n), 2)); i++)
		{
			if(mrt(n, 2+i) == true)
				return true;
		}
		return false;
	}
	
	public static ArrayList<Long> sieve(long n)
	{
		boolean prime[] = new boolean[(int)n + 1];
		Arrays.fill(prime, true);
		prime [0] = false;
		prime [1] = false;
		
		ArrayList<Long> result = new ArrayList<>();
		
		 
 
        for (long p = 2; pow(p, 2)  <= n; p++) // If prime[p] is true, then it is a prime
        {
            if (prime[(int)p] == true)
            {
            	//result.add(p);
                // Update all multiples of p
                for (long i = p * p; i <= n; i += p)
                    prime[(int)i] = false;
            }
        }
        
        for (long i = 2; i <= n; i++)
        {
            if (prime[(int)i] == true)
                result.add(i);
        }
       return result;
	}

}
