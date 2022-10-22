/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import org.junit.Test;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class DumpAsJsonTest extends ModelCheckerTestCase {

	public DumpAsJsonTest() {
		super("Github757", new String[] { "-config", "Github757.tla", "-dump", "json",
				System.getProperty("java.io.tmpdir") + File.separator + "DumpAsJsonTest" }, ExitStatus.VIOLATION_SAFETY);
	}

	// Multiple -dump flags cause weirdness, e.g. dump.json with dot content inside
	@Override
	protected boolean doDump() {
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));

		// -dump json appends the ".json" extension to the file name
		final File dumpFile = new File(System.getProperty("java.io.tmpdir") + File.separator + "DumpAsJsonTest.json");
		assertTrue(dumpFile.exists());

		// If the file exists, simply compare it to a correct and manually checked version.
		final InputStream master = getClass().getResourceAsStream("DumpAsJsonTest.json");
		assertTrue(Arrays.equals(DumpAsDotTest.getBytes(master), DumpAsDotTest.getBytes(new FileInputStream(dumpFile))));

		assertZeroUncovered();
	}
}
