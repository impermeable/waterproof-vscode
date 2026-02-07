import React from "react";
import { createRoot } from "react-dom/client";

import "../styles/index";
// get the react panel
import Execute from "./execute";

const container = document.getElementById("root");
// createRoot(container!) if you use TypeScript
const root = createRoot(container!);
// render the execute panel
root.render(
    <React.StrictMode>
        <Execute />
    </React.StrictMode>
);
